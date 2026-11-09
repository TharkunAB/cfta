import MicroCFTA.SourceCurrentConjunctionRequirementPullMemos
import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed

/-!
# Ordered memo receipts for successful shared-cell forces

A pending cell records the exact deferred projection sequence at its
actual physical endpoint. Completed cells, columns, and canonicalization
add no global calls. Missing handles cannot return successfully. Failed
terminal projections remain outside these successful receipts. They are
not classified as operations without reads.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsMemos
open Cache InternedConstructorTemplates
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementCells
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "canonical" => SourceCurrentConjunctionRequirements.canonical
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A successful cell step retains either no read or its sole actual cursor step. -/
inductive ForceStepReads : {p h handle : Nat} → {before after : Cells} →
    {event : Event Symbol FullSyntax.Formula} →
    (forceStep p h handle before = .done event after) → Memos → Memos → Prop where
  | hit {p h handle : Nat} {before : Cells} {nodes : List Node} {memos : Memos}
      (found : lookup handle before = some (.done nodes))
      {actual : forceStep p h handle before = .done (.complete nodes) before} :
      ForceStepReads actual memos memos
  | column {p h handle : Nat} {before : Cells} {nodes : List Node} {memos : Memos}
      (found : lookup handle before = some (.column nodes))
      {actual : forceStep p h handle before =
        .done (.complete (canonical nodes)) (update handle (.done (canonical nodes)) before)} :
      ForceStepReads actual memos memos
  | complete {p h handle : Nat} {before : Cells} {physical : Physical}
      {cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol FullSyntax.Formula}
      {nodes : List Node} {memos saved : Memos}
      (found : lookup handle before = some (.pending cursor))
      (calls : SourceCurrentConjunctionRequirementPullMemos.StepReads p h cursor before.physical
        (.complete nodes) physical memos saved)
      {actual : forceStep p h handle before =
        .done (.complete nodes) (update handle (.done nodes) {before with physical := physical})} :
      ForceStepReads actual memos saved
  | more {p h handle : Nat} {before : Cells} {physical : Physical}
      {cursor next : SourceCurrentConjunctionRequirementPull.Cursor Symbol FullSyntax.Formula}
      {memos saved : Memos}
      (found : lookup handle before = some (.pending cursor))
      (calls : SourceCurrentConjunctionRequirementPullMemos.StepReads p h cursor before.physical
        (.more next) physical memos saved)
      {actual : forceStep p h handle before =
        .done (.more next) (update handle (.pending next) {before with physical := physical})} :
      ForceStepReads actual memos saved

/-- A successful force retains its exact cursor calls and cell-publication endpoint. -/
inductive ForceReads : {p h handle : Nat} → {before after : Cells} → {nodes : List Node} →
    (force p h handle before = .done nodes after) → Memos → Memos → Prop where
  | hit {p h handle : Nat} {before : Cells} {nodes : List Node} {memos : Memos}
      (found : lookup handle before = some (.done nodes))
      {actual : force p h handle before = .done nodes before} : ForceReads actual memos memos
  | column {p h handle : Nat} {before : Cells} {nodes : List Node} {memos : Memos}
      (found : lookup handle before = some (.column nodes))
      {actual : force p h handle before =
        .done (canonical nodes) (update handle (.done (canonical nodes)) before)} :
      ForceReads actual memos memos
  | pending {p h handle : Nat} {before after : Cells}
      {cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol FullSyntax.Formula}
      {nodes : List Node} {memos saved : Memos}
      {actual : force p h handle before = .done nodes after}
      (found : lookup handle before = some (.pending cursor))
      (calls : SourceCurrentConjunctionRequirementPullMemos.RunReads p h cursor before.physical
        nodes after.physical memos saved) : ForceReads actual memos saved

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem pending_inputs (before : Cells) (handle : Nat)
    (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol FullSyntax.Formula)
    (found : lookup handle before = some (.pending cursor))
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before) :
    SourceCurrentConjunctionCompletionReads.Inputs before.physical.heap cursor.pending := by
  intro job member
  exact ⟨(values handle (.pending cursor) found).2 job member,
    (closed handle (.pending cursor) found).2 job member⟩

/-- Actual successful cell steps derive their own coherent returned memo bundle. -/
theorem forceStep_memos {p h handle : Nat} {before after : Cells}
    {event : Event Symbol FullSyntax.Formula}
    (actual : forceStep p h handle before = .done event after) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (memos : Memos) (valid : Valid before.physical.heap memos) :
    ∃ saved, ForceStepReads actual memos saved ∧ Valid after.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases found : lookup handle before with
  | none =>
      simp only [forceStep, found] at actual
      cases actual
  | some cell =>
      cases cell with
      | done nodes =>
          simp only [forceStep, found] at actual
          cases actual
          exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
      | column nodes =>
          simp only [forceStep, found] at actual
          cases actual
          exact ⟨memos, .column found, valid, extends_refl _, rfl⟩
      | pending cursor =>
          have inputs := pending_inputs before handle cursor found values closed
          cases observed : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
          | failed fault physical =>
              simp only [forceStep, found, observed] at actual
              cases actual
          | done event physical =>
              cases event with
              | complete nodes =>
                  simp only [forceStep, found, observed] at actual
                  cases actual
                  obtain ⟨saved, calls, coherent, retained, same⟩ :=
                    SourceCurrentConjunctionRequirementPullMemos.step_memos observed ready inputs memos valid
                  exact ⟨saved, .complete found calls, coherent, retained, same⟩
              | more next =>
                  simp only [forceStep, found, observed] at actual
                  cases actual
                  obtain ⟨saved, calls, coherent, retained, same⟩ :=
                    SourceCurrentConjunctionRequirementPullMemos.step_memos observed ready inputs memos valid
                  exact ⟨saved, .more found calls, coherent, retained, same⟩

/-- Complete successful forcing derives every actual read without a future receipt premise. -/
theorem force_memos {p h handle : Nat} {before after : Cells} {nodes : List Node}
    (actual : force p h handle before = .done nodes after) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (memos : Memos) (valid : Valid before.physical.heap memos) :
    ∃ saved, ForceReads actual memos saved ∧ Valid after.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases found : lookup handle before with
  | none =>
      rw [force_step, forceStep_missing p h handle before found] at actual
      cases actual
  | some cell =>
      cases cell with
      | done cached =>
          rw [force_hit p h handle cached before found] at actual
          cases actual
          exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
      | column column =>
          have completed : force p h handle before =
              .done (canonical column) (update handle (.done (canonical column)) before) := by
            rw [force_step]
            simp only [forceStep, found]
          have same := completed.symm.trans actual
          cases same
          exact ⟨memos, .column found, valid, extends_refl _, rfl⟩
      | pending cursor =>
          have corresponding := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
          obtain ⟨saved, calls, coherent, retained, same⟩ :=
            SourceCurrentConjunctionRequirementPullMemos.run_memos corresponding ready
              (pending_inputs before handle cursor found values closed) memos valid
          exact ⟨saved, .pending found calls, coherent, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsMemos
