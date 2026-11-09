import MicroCFTA.SourceCurrentConjunctionSharedWorklistRunFrame
import MicroCFTA.SourceCurrentConjunctionSharedWorklistCoverage
import MicroCFTA.SourceCurrentConjunctionSharedWorklistTableRead

/-!
# Materialization at the actual original-query endpoint

Original initialization derives handle validity and scheduling coverage.
The finite actual execution preserves both properties. A drained queue has
only completed private cells. Its table can be read in full without another
native observation or worker step. Failed execution retains its exact state.
This result does not yet establish Boolean soundness or selected caller use.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistTerminalMaterialization
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep (Outcome)
open SourceCurrentConjunctionSharedWorklistRun (Run explore)
open SourceCurrentConjunctionSharedWorklistMaterialization (CellsCached SpinesCached readTable)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "Valid" => SourceCurrentConjunctionSharedWorklistHandleValidity.Valid
local notation "Covered" => SourceCurrentConjunctionSharedWorklistCoverage.Covered

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem graph_invariants {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : Run p h before outcome) :
    Valid before → Covered before → Valid outcome.state ∧ Covered outcome.state := by
  induction actual with
  | failed observed =>
      intro valid covered
      have nextValid := SourceCurrentConjunctionSharedWorklistHandleValidity.step_valid p h _ valid
      have nextCovered := SourceCurrentConjunctionSharedWorklistCoverage.step_covered p h _ covered
      simpa only [observed, Outcome.state] using And.intro nextValid nextCovered
  | drained observed =>
      intro valid covered
      have nextValid := SourceCurrentConjunctionSharedWorklistHandleValidity.step_valid p h _ valid
      have nextCovered := SourceCurrentConjunctionSharedWorklistCoverage.step_covered p h _ covered
      simpa only [observed, Outcome.state] using And.intro nextValid nextCovered
  | more observed _ ih =>
      intro valid covered
      have nextValid := SourceCurrentConjunctionSharedWorklistHandleValidity.step_valid p h _ valid
      have nextCovered := SourceCurrentConjunctionSharedWorklistCoverage.step_covered p h _ covered
      rw [observed] at nextValid nextCovered
      exact ih nextValid nextCovered

private theorem graph_terminal {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : Run p h before outcome) :
    (∃ fault after, outcome = .failed fault after) ∨ (∃ after, outcome = .done .drained after) := by
  induction actual with
  | failed _ => exact Or.inl ⟨_, _, rfl⟩
  | drained _ => exact Or.inr ⟨_, rfl⟩
  | more _ _ ih => exact ih

/-- The original query derives handle validity and scheduling coverage at its exact endpoint. -/
theorem explore_invariants (p h budget : Nat) (start : Node) (before : Physical) :
    Valid (explore p h budget start before).state ∧ Covered (explore p h budget start before).state :=
  graph_invariants (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistHandleValidity.initial budget start before)
    (SourceCurrentConjunctionSharedWorklistCoverage.initial_covered budget start before)

/-- A drained original-query execution derives every premise of complete pure table reading. -/
theorem explore_materializable (p h budget : Nat) (start : Node) (before : Physical)
    (after : WorkState) (actual : explore p h budget start before = .done .drained after) :
    CellsCached after.storage ∧ SpinesCached after.storage ∧
      ∃ credits table, SourceCurrentConjunctionRequirementRowsOrigins.Credits credits after.storage ∧
        (∀ credit ∈ credits, credit ≤ budget) ∧ readTable credits after = some table ∧
        table.map (fun entry => entry.nodes) = after.table.map (fun entry => entry.nodes) := by
  have invariants := explore_invariants p h budget start before
  rw [actual] at invariants
  obtain ⟨valid, covered⟩ := invariants
  have empty := SourceCurrentConjunctionSharedWorklistRunFrame.explore_done_pending
    p h budget start before after actual
  obtain ⟨cells, spines⟩ := SourceCurrentConjunctionSharedWorklistCoverage.drained_cached after covered empty
  obtain ⟨frame, same⟩ := SourceCurrentConjunctionSharedWorklistRunFrame.explore_frame
    p h budget start before
  rw [actual] at same
  change frame.state = after at same
  have creditValid : SourceCurrentConjunctionRequirementRowsOrigins.Credits frame.credits after.storage := by
    rw [← same]
    exact frame.valid
  obtain ⟨table, read⟩ := SourceCurrentConjunctionSharedWorklistTableRead.readTable_complete
    frame.credits after creditValid cells spines valid
  exact ⟨cells, spines, frame.credits, table, creditValid, frame.bounded, read,
    SourceCurrentConjunctionSharedWorklistTableRead.readTable_nodes frame.credits after table read⟩

/-- Finite original-query execution returns an exact fault or a completely readable cached table. -/
theorem explore_total (p h budget : Nat) (start : Node) (before : Physical) :
    (∃ fault after, explore p h budget start before = .failed fault after) ∨
      ∃ after credits table, explore p h budget start before = .done .drained after ∧
        CellsCached after.storage ∧ SpinesCached after.storage ∧
        SourceCurrentConjunctionRequirementRowsOrigins.Credits credits after.storage ∧
        (∀ credit ∈ credits, credit ≤ budget) ∧ readTable credits after = some table ∧
        table.map (fun entry => entry.nodes) = after.table.map (fun entry => entry.nodes) := by
  rcases graph_terminal (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    with failed | drained
  · exact Or.inl failed
  · obtain ⟨after, actual⟩ := drained
    obtain ⟨cells, spines, credits, table, valid, bounded, read, order⟩ :=
      explore_materializable p h budget start before after actual
    exact Or.inr ⟨after, credits, table, actual, cells, spines, valid, bounded, read, order⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistTerminalMaterialization
