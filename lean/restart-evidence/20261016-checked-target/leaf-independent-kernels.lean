import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
namespace MicroCFTA.AllocatedLeafIndependentKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State advance store SlotReceipt)
open SourceCurrentAllocatedSharedTargetForce (Force)
open SourceCurrentAllocatedSharedTargetLeaf
open SourceEqualityClassTarget (operandPaths)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- A literal hit executes the next query at the identical checked entry and keeps all target slots and merge entries.
example {record : Record} {values : List (Value Symbol Guard)} {path : Path} {input target result : Value Symbol Guard}
 {before : State width} {checked : Checked width} (present : before.targets path = some target)
 (step : SourceCurrentAllocatedTargetQuery.Step target input before.checked result checked) :
 Leaf record values path input before result (advance before checked) ∧
 (advance before checked).targets path = some target ∧ (advance before checked).memo = before.memo :=
 ⟨.apply (.hit present) step, present, rfl⟩

-- A literal miss stores the actual target return before the leaf query and keeps that exact merge winner table.
example {record : Record} {values : List (Value Symbol Guard)} {path : Path} {input target result : Value Symbol Guard}
 {before : State width} {middle checked : Checked width} {saved : Memo} (absent : before.targets path = none)
 (targeted : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
  before.checked before.memo target middle saved)
 (step : SourceCurrentAllocatedTargetQuery.Step target input middle result checked) :
 Leaf record values path input before result (advance (store before path target middle saved) checked) ∧
 (advance (store before path target middle saved) checked).targets path = some target ∧
 (advance (store before path target middle saved) checked).memo = saved := by
 exact ⟨.apply (.miss absent targeted) step, by simp only [advance, store, put, ite_true], rfl⟩

section Initial
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
 (before : State width) (ready : Ready formulas solver inventory record values base before) (known : Values base values)
 (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
 (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
 (path : Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
 (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
 (ranges : Ranges record values path input before) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)

-- Initial selected domains and reached range checks construct the actual leaf without supplied Force/Step completion.
example : ∃ result after next final,
 Leaf record values path input before result after ∧
 Ready formulas solver next record values base after ∧ result.free = [] ∧
 Valid after.checked.native.machine.heap final := by
 obtain ⟨result, after, next, final, receipt⟩ := complete formulas solver inventory record values base before ready known domains
  coherent active path member input available closed ranges memos valid
 exact ⟨result, after, next, final, receipt.actual, receipt.ready, receipt.closed, receipt.globals.valid⟩

-- An independently supplied actual leaf gets narrowing and conditional preservation at the same exact return.
example {result : Value Symbol Guard} {after : State width}
 (actual : Leaf record values path input before result after) :
 ∃ next final,
 Receipt formulas solver next record values base path input before result after memos final ∧
 (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term) ∧
 (∀ ambient symbol terms part,
  All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
  EqualityNormalize.ClassSat (.node symbol terms) record.paths → (Term.node symbol terms).atPath path = some part →
  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input part →
  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part) := by
 obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known domains coherent active member
  available closed ranges memos valid
 exact ⟨next, final, receipt, receipt.narrows, receipt.preserves⟩
end Initial

section Returned
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
 {inventory : Inventory} {record : Record} {values : List (Value Symbol Guard)}
 {base : InternedConstructorTemplates.State Symbol Guard} {path : Path} {input result : Value Symbol Guard}
 {before after : State width} {memos final : Memos}
 (receipt : Receipt formulas solver inventory record values base path input before result after memos final)

-- The actual heap effects retain the same fourth table's soundness without invoking any old decision body.
example (fourth : SourceCurrentEmptinessMemo.Memo)
 (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap fourth) :
 SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap fourth :=
 receipt.fourth_correct fourth correct

-- Each old slot has its literal value and historical receipt after the computed inventory advance.
example (other : Path) (target : Value Symbol Guard) (found : before.targets other = some target) :
 after.targets other = some target ∧
 SlotReceipt width formulas solver record values after.checked.native.machine.heap after.memo other target ∧
 Available after.checked.native.machine.heap target ∧ target.free = [] := by
 have present := receipt.slots other target found
 have slot := receipt.ready.receipts other target present
 exact ⟨present, slot, slot.available⟩

-- The same global bundle has a valid final heap, retained unfolding entries, and unchanged predicate/descendant tables.
example : Valid after.checked.native.machine.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query :=
 ⟨receipt.globals.valid, receipt.globals.retained, receipt.globals.query⟩
end Returned
end MicroCFTA.AllocatedLeafIndependentKernels
