import MicroCFTA.SourceCurrentAllocatedLocalWorker

/-!
# Literal Scan and Required preparation before class editing

The prefix retains the same original records, checked states, and memos.
A stopped Scan erases the original forest. A successful Scan runs Required
before the class pass. The factorization theorem retains the full source
worker, including every failed phase observation.
-/
namespace MicroCFTA.SourceCurrentScanRequiredWorker
open EqualityNormalize InternedConstructorTemplates SourceEqualityClassOrder
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Outcome" => SourceCurrentAllocatedLocalWorker.Outcome
local notation "scan" => SourceCurrentAllocatedLocalWorker.scan
local notation "required" => SourceCurrentAllocatedLocalWorker.required
local notation "pass" => SourceCurrentAllocatedLocalWorker.pass
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A preparation result retains the outcome, exact selected records, and returned forest. -/
abbrev Result := Option Class × List Record × List (Value Symbol Guard)

/-- Execute the literal source prefix and omit class editing until the continuation. -/
noncomputable def prepare (g s r p h n budget : Nat) (records : List Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) : Outcome Result width :=
  (scan g s p h n budget records values before fourth memo).bind fun selected middle saved current =>
    match selected.1 with
    | some paths => .done (some paths, selected.2, EqualityLeafProjectionRuntimeEmpty.erase values) middle saved current
    | none => (required r h (SourceEqualitySelectedRequired.paths (selected.2.map Record.paths))
        values middle saved current).bind fun results after final warm => .done (none, selected.2, results) after final warm

/-- Preparation followed by its reached class pass is exactly the original local classes worker. -/
theorem classes (g s r e p h m c n budget : Nat) (records : List Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo =
      (prepare g s r p h n budget records values before fourth memo).bind fun result after saved current =>
        match result.1 with
        | some _ => .done result.2.2 after saved current
        | none => pass e p h m c n result.2.1 result.2.2 after saved current := by
  unfold SourceCurrentAllocatedLocalWorker.classes prepare
  cases actual : scan g s p h n budget records values before fourth memo with
  | failed => rfl
  | done result middle saved current =>
      obtain ⟨outcome, kept⟩ := result
      cases outcome with
      | some paths => rfl
      | none =>
          cases required r h (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle saved current <;> rfl

end MicroCFTA.SourceCurrentScanRequiredWorker
