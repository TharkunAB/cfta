import MicroCFTA.SourceCurrentAllocatedSharedTargetState

/-!
# Actual checked forcing of class-local target slots

A hit returns the stored target and the identical state. A miss runs the
new checked class target before storing its exact return. Historical slot
receipts retain earlier targets when the input inventory changes. Neither
branch resets native tables, equality operations, or the warm merge memo.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetForce
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState
open SourceEqualityClassTarget (operandPaths)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat}

/-- Every earlier returned slot retains the same literal value. -/
def Retains (before after : State width) : Prop :=
  ∀ path value, before.targets path = some value → after.targets path = some value

theorem Retains.refl (state : State width) : Retains state state := fun _ _ present => present

theorem Retains.trans {before middle after : State width}
    (first : Retains before middle) (later : Retains middle after) : Retains before after :=
  fun path value present => later path value (first path value present)

theorem advance_retains (before : State width) (checked : Checked width) :
    Retains before (advance before checked) := fun _ _ present => present

/-- Raw forcing records only the actual slot branch and completed target graph. -/
inductive Force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) :
    State width → Value Symbol Guard → State width → Prop where
  | hit (present : before.targets path = some value) : Force record values path before value before
  | miss (absent : before.targets path = none)
      (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
        before.checked before.memo value checked saved) :
      Force record values path before value (store before path value checked saved)

/-- A hit adds no calls. A miss retains the same actual target reads. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} → {path : EqualityNormalize.Path} →
    {before after : State width} → {value : Value Symbol Guard} →
    Force record values path before value after → Memos → Memos → Prop where
  | hit {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before : State width} {value : Value Symbol Guard}
      (present : before.targets path = some value) (memos : Memos) :
      Reads formulas solver (record := record) (values := values)
        (Force.hit (record := record) (values := values) present) memos memos
  | miss {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before : State width} {value : Value Symbol Guard} {checked : Checked width} {saved : Memo}
      (absent : before.targets path = none)
      {actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
        before.checked before.memo value checked saved}
      (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final) :
      Reads formulas solver (record := record) (values := values)
        (Force.miss absent actual) memos final

/-- Missing slots require only the reached checks of their actual target construction. -/
def ForceRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (before : State width) : Prop :=
  before.targets path = none → SourceCurrentAllocatedTargetGraph.TargetRanges
    values (operandPaths record.paths path) before.checked before.memo

/-- The same actual force derives the new inventory, stored slot, and warm table receipts. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (path : EqualityNormalize.Path)
    (before : State width) (value : Value Symbol Guard) (after : State width) (memos final : Memos) : Prop where
  actual : Force record values path before value after
  reads : Reads formulas solver actual memos final
  ready : Ready formulas solver inventory record values base after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  extension : SourceRecursiveIntersectionKernel.Extension before.checked.native.machine after.checked.native.machine
  available : Available after.checked.native.machine.heap value
  closed : value.free = []
  present : after.targets path = some value
  slots : Retains before after
  retained : Extends before.memo after.memo
  globals : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap after.checked.native.machine.heap memos final
  included : SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value

private theorem miss_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before : State width} {value : Value Symbol Guard} {checked : Checked width} {saved : Memo} {memos final : Memos}
    (ready : Ready formulas solver inventory record values base before) (member : path ∈ record.paths)
    (absent : before.targets path = none)
    (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
      before.checked before.memo value checked saved)
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
      before.checked before.memo value checked saved memos final)
    (included : SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value) :
    Receipt formulas solver next record values base path before value (store before path value checked saved) memos final := by
  refine ⟨.miss absent actual, .miss absent reads, ready.store path member actual reads receipt,
    receipt.effects, receipt.extension, receipt.available, receipt.closed, ?_, ?_, receipt.retained,
    receipt.globals, included⟩
  · simp only [store, put, ite_true]
  · intro other target present
    by_cases same : other = path
    · subst other
      rw [absent] at present
      cases present
    · simpa only [store, put, same, ite_false] using present

/-- Initial class facts verify a raw force at its exact actual return. -/
theorem Force.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {value : Value Symbol Guard}
    (actual : Force record values path before value after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next final, Receipt formulas solver next record values base path before value after memos final := by
  cases actual with
  | hit present =>
      have slot := ready.receipts path value present
      have available := slot.available
      have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (physical before.checked) :=
        ⟨ready.checked.semantic, ready.checked.costs, ready.checked.good.operations, ready.checked.good.fields⟩
      have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
      exact ⟨inventory, memos, ⟨.hit present, .hit present memos, ready, effects, .refl _,
        available.1, available.2, present, Retains.refl _, extends_refl _,
        ⟨effects.keeps, ready.checked.semantic, ready.checked.costs, valid, extends_refl _, rfl⟩,
        slot.included coherent active⟩⟩
  | miss absent target =>
      have available : Values before.checked.native.machine.heap values := fun value member =>
        ready.captured.available value (known value member)
      obtain ⟨next, final, reads, receipt, included⟩ := SourceCurrentAllocatedClassTarget.actual_verified
        formulas solver inventory record coherent active path member values target ready.checked ready.admitted
        available domains ready.stored ready.covered (ranges absent) memos valid
      exact ⟨next, final, miss_receipt ready member absent target reads receipt included⟩

/-- Initial readiness and reached ranges construct first forcing or literal reuse of a stored target. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ value after next final, Force record values path before value after ∧
      Receipt formulas solver next record values base path before value after memos final := by
  cases present : before.targets path with
  | some value =>
      have actual : Force record values path before value before := .hit present
      obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known domains coherent active member ranges memos valid
      exact ⟨value, before, next, final, actual, receipt⟩
  | none =>
      have available : Values before.checked.native.machine.heap values := fun value member =>
        ready.captured.available value (known value member)
      obtain ⟨value, checked, saved, next, final, target, reads, receipt, included⟩ :=
        SourceCurrentAllocatedClassTarget.finite formulas solver inventory record coherent active path member values
          before.checked before.memo ready.checked ready.admitted available domains ready.stored ready.covered
          (ranges present) memos valid
      have returned := miss_receipt ready member present target reads receipt included
      exact ⟨value, _, next, final, returned.actual, returned⟩

/-- Force never calls the fourth memo. Its heap growth retains an earlier Correct table unchanged. -/
theorem Receipt.fourth_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {value : Value Symbol Guard} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values base path before value after memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap fourth :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps fourth correct

end MicroCFTA.SourceCurrentAllocatedSharedTargetForce
