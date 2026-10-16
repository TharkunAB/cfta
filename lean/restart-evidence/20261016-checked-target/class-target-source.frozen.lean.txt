import MicroCFTA.SourceCurrentAllocatedTargetComplete
import MicroCFTA.SourceCurrentTargetPathComplete

/-!
# Checked targets for actual retained equality classes

Each target uses the ordered other paths of its captured class forest.
Selected path closure supplies finite projection and merge. Actual checked
queries derive the returned inventory. Class satisfaction supplies a common
selected subterm. Other ordinary siblings can remain open.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassTarget
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityClassTarget (operandPaths operandPaths_nonempty operandPaths_nonroot)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable {width : Nat}

/-- A target retains the selected subterm of each accepted class-satisfying captured forest. -/
def SelectedIncludes
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : Path) (result : Value Symbol Guard) : Prop :=
  ∀ ambient symbol terms part,
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
    ClassSat (.node symbol terms) record.paths →
    (Term.node symbol terms).atPath path = some part →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part

/-- The actual target receipt and class equality derive selected-subterm inclusion. -/
theorem receipt_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : Path} {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver inventory values
      (operandPaths record.paths path) before memo result after saved memos final)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (member : path ∈ record.paths) : SelectedIncludes formulas solver record values path result := by
  intro ambient symbol terms part accepted satisfied selected
  apply receipt.included (operandPaths_nonempty record.paths active path)
    (operandPaths_nonroot record coherent active path) ambient symbol terms part accepted
  intro other included
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp included
  obtain ⟨common, selectedAt, otherAt⟩ := class_pair_equal (.node symbol terms) record.paths active satisfied
    path original member (List.mem_filter.mp originalIn).1
  have samePart := Option.some.inj (selectedAt.symm.trans selected)
  subst common
  simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherAt

/-- Initial selected class domains construct the same checked target, global reads, and selected language. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values (operandPaths record.paths path) before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final,
      ∃ actual : Target values (operandPaths record.paths path) before memo result after saved,
        SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
        SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values
          (operandPaths record.paths path) before memo result after saved memos final ∧
        SelectedIncludes formulas solver record values path result := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedTargetComplete.target_complete formulas solver inventory values
      (operandPaths record.paths path) before memo ready admitted available
      (SourceCurrentTargetPathComplete.operand_domains record values domains path) stored covered ranges memos valid
  exact ⟨result, after, saved, next, final, actual, reads, receipt,
    receipt_included receipt coherent active member⟩

/-- Initial class facts verify an existing actual target at its exact returned value and full state. -/
theorem actual_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Target values (operandPaths record.paths path) before memo result after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values (operandPaths record.paths path) before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next final, SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values
        (operandPaths record.paths path) before memo result after saved memos final ∧
      SelectedIncludes formulas solver record values path result := by
  obtain ⟨next, final, reads, receipt⟩ := SourceCurrentAllocatedTargetComplete.Target.verified formulas solver inventory actual
    ready admitted available (SourceCurrentTargetPathComplete.operand_domains record values domains path)
    stored covered ranges memos valid
  exact ⟨next, final, reads, receipt, receipt_included receipt coherent active member⟩

end MicroCFTA.SourceCurrentAllocatedClassTarget
