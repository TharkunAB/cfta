import MicroCFTA.SourceCurrentConjunctionRequirementCells

/-!
# Exact execution of a pending shared cell

A pending cell executes the same deferred cursor run. Cell publication does
not change its native physical endpoint. A projection fault retains the
final stopped cursor at the same handle. Cached hits, columns, and missing
handles have separate branches and are not identified with pending runs.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRequirementCells
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Cursor" => SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private def Corresponds (p h handle : Nat) (cursor : Cursor) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (List Node) → Prop
  | .done nodes after =>
      SourceCurrentConjunctionRequirementPull.run p h cursor before = .done nodes after.physical
  | .failed diagnostic after => ∃ stopped fault,
      diagnostic = .projection handle stopped fault ∧
      SourceCurrentConjunctionRequirementPull.run p h cursor before = .failed fault after.physical ∧
      lookup handle after = some (.pending stopped)

private theorem pending_corresponds (p h handle : Nat) (before : Cells) (cursor : Cursor)
    (found : lookup handle before = some (.pending cursor)) :
    Corresponds p h handle cursor before.physical (force p h handle before) := by
  suffices ∀ weight (current : Cells) (pending : Cursor), remaining handle current = weight →
      lookup handle current = some (.pending pending) →
      Corresponds p h handle pending current.physical (force p h handle current) by
    exact this _ before cursor rfl found
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current pending measured present
      rw [force_step]
      cases observed : SourceCurrentConjunctionRequirementPull.step p h pending current.physical with
      | failed fault physical =>
          simp only [forceStep, present, observed]
          refine ⟨pending, fault, rfl, ?_, present⟩
          rw [SourceCurrentConjunctionRequirementPull.run_step, observed]
          rfl
      | done event physical =>
          cases event with
          | complete nodes =>
              simp only [forceStep, present, observed]
              change SourceCurrentConjunctionRequirementPull.run p h pending current.physical =
                .done nodes physical
              rw [SourceCurrentConjunctionRequirementPull.run_step, observed]
              rfl
          | more next =>
              let updated := update handle (.pending next) {current with physical := physical}
              have first : forceStep p h handle current = .done (.more next) updated := by
                simp only [forceStep, present, observed, updated]
              have decreased : remaining handle updated < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current updated next first
              have retained : lookup handle updated = some (.pending next) :=
                lookup_update handle (.pending pending) (.pending next)
                  {current with physical := physical} present
              have later := smaller _ decreased updated next rfl retained
              simp only [forceStep, present, observed]
              change Corresponds p h handle pending current.physical (force p h handle updated)
              cases result : force p h handle updated with
              | done nodes after =>
                  rw [result] at later
                  change SourceCurrentConjunctionRequirementPull.run p h pending current.physical =
                    .done nodes after.physical
                  rw [SourceCurrentConjunctionRequirementPull.run_step, observed]
                  exact later
              | failed diagnostic after =>
                  rw [result] at later
                  obtain ⟨stopped, fault, named, completed, cached⟩ := later
                  refine ⟨stopped, fault, named, ?_, cached⟩
                  rw [SourceCurrentConjunctionRequirementPull.run_step, observed]
                  exact completed

/-- A successful pending force has the same nodes and physical endpoint as the literal cursor run. -/
theorem force_pending_run {p h handle : Nat} {before after : Cells} {cursor : Cursor} {nodes : List Node}
    (found : lookup handle before = some (.pending cursor))
    (actual : force p h handle before = .done nodes after) :
    SourceCurrentConjunctionRequirementPull.run p h cursor before.physical = .done nodes after.physical := by
  have corresponding := pending_corresponds p h handle before cursor found
  rw [actual] at corresponding
  exact corresponding

/-- A failed pending force retains the final stopped cursor and its exact projection fault. -/
theorem force_pending_failed {p h handle : Nat} {before after : Cells} {cursor : Cursor}
    {diagnostic : Fault Symbol Formula}
    (found : lookup handle before = some (.pending cursor))
    (actual : force p h handle before = .failed diagnostic after) :
    ∃ stopped fault, diagnostic = .projection handle stopped fault ∧
      SourceCurrentConjunctionRequirementPull.run p h cursor before.physical = .failed fault after.physical ∧
      lookup handle after = some (.pending stopped) := by
  have corresponding := pending_corresponds p h handle before cursor found
  rw [actual] at corresponding
  exact corresponding

end MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
