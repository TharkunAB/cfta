import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationGraph
import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
import MicroCFTA.SourceCurrentConjunctionTableSoundness

/-!
# Physical domain of the actual materialized table

Admission never stores an original query containing Empty. Actual finite
execution preserves that fact on successful and failed outcomes. The same
cached table reader retains query operands and reads each requirement from
its exact current done cell. Current residency and closedness therefore
supply the stored-domain premises of finite-table soundness.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStoredDomain
open Language
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistMaterialization
open SourceCurrentConjunctionSharedWorklistMaterializationGraph (RowsRead)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

/-- Every actual stored query excludes the Empty constructor. -/
def NoEmptyTable (before : WorkState) : Prop := ∀ entry ∈ before.table, .empty ∉ entry.nodes

/-- The literal empty initial table excludes Empty without an input closedness premise. -/
theorem initial_noEmpty (budget : Nat) (start : Node) (before : Physical) :
    NoEmptyTable (initial budget start before) := by
  intro entry member
  cases member

section Execution
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit retains old queries and stores a new query only after its Empty test. -/
theorem visit_noEmpty (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (safe : NoEmptyTable before) : NoEmptyTable (visit h nodes rest before).state := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact safe
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact safe
      | false =>
          have nonempty : (.empty : Node) ∉ nodes := by
            intro member
            have present := (SourceCurrentConjunctionRequirements.any_empty nodes).mpr member
            rw [empty] at present
            cases present
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact safe
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact safe
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      intro entry member
                      rcases List.mem_cons.mp member with same | old
                      · cases same
                        exact nonempty
                      · exact safe entry old
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      intro entry member
                      rcases List.mem_cons.mp member with same | old
                      · cases same
                        exact nonempty
                      · exact safe entry old

/-- Successful and failed shared steps preserve exclusion of Empty from the stored table. -/
theorem step_noEmpty (p h : Nat) (before : WorkState) (safe : NoEmptyTable before) :
    NoEmptyTable (step p h before).state := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact safe
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_noEmpty h nodes rest before safe
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact safe
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact safe
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_noEmpty h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} safe
      | rows handle =>
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact safe
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact safe
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact safe

/-- An actual finite run retains the query-domain assertion at its exact final or fault state. -/
theorem run_noEmpty {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (safe : NoEmptyTable before) : NoEmptyTable outcome.state := by
  revert safe
  induction actual with
  | failed advanced =>
      intro safe
      simpa only [advanced, Outcome.state] using step_noEmpty p h _ safe
  | drained advanced =>
      intro safe
      simpa only [advanced, Outcome.state] using step_noEmpty p h _ safe
  | more advanced rest ih =>
      intro safe
      apply ih
      simpa only [advanced, Outcome.state] using step_noEmpty p h _ safe

/-- Original initialization derives exclusion of Empty at every actual exploration outcome. -/
theorem explore_noEmpty (p h budget : Nat) (start : Node) (before : Physical) :
    NoEmptyTable (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state :=
  run_noEmpty (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (initial_noEmpty budget start before)
end Execution

private theorem row_values (before : Storage)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before.requirements)
    (handles : List Nat) (row : List (List Node)) (actual : readRow handles before = some row) :
    ∀ nodes ∈ row, Values before.requirements.physical.heap nodes := by
  have aligned := SourceCurrentConjunctionSharedWorklistMaterializationGraph.readRow_graph handles before row actual
  clear actual
  induction aligned with
  | nil => intro nodes member; cases member
  | @cons handle nodes handles rows found rest ih =>
      intro selected member
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact values handle (.done nodes) found
      · exact ih selected later

private theorem rows_values {credits : List Nat} {before : Storage} {handle : Nat}
    {rows : List (List (List Node))} (actual : RowsRead credits before handle rows)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before.requirements) :
    ∀ row ∈ rows, ∀ nodes ∈ row, Values before.requirements.physical.heap nodes := by
  induction actual with
  | nil own cached => intro row member; cases member
  | cons own cached head nextFound smaller rest ih =>
      intro row member
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact row_values before values _ _ head
      · exact ih row later

/-- The same actual cached-table read has resident requirements and closed nonempty original queries. -/
theorem readTable_domain (credits : List Nat) (before : WorkState)
    (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (actual : readTable credits before = some table)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before) (safe : NoEmptyTable before) :
    SourceCurrentConjunctionTableSoundness.StoredDomain .empty SourceCurrentConjunctionWorklist.closed
      (Available before.storage.requirements.physical.heap) table := by
  intro result member
  obtain ⟨original, originalIn, aligned⟩ :=
    SourceCurrentConjunctionSharedWorklistMaterializationGraph.readTable_member credits before table actual result member
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [aligned.1]
    apply List.all_eq_true.mpr
    intro node included
    exact List.isEmpty_iff.mpr (closed.table original originalIn node included)
  · rw [aligned.1]
    exact safe original originalIn
  · rw [aligned.1]
    exact values.table original originalIn
  · intro row rowIn nodes nodesIn value valueIn
    cases selected : original.rows with
    | none =>
        have empty : result.rows = [] := by simpa only [selected] using aligned.2
        rw [empty] at rowIn
        cases rowIn
    | some handle =>
        have read : RowsRead credits before.storage handle result.rows := by
          simpa only [selected] using aligned.2
        exact rows_values read values.cells row rowIn nodes nodesIn value valueIn

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStoredDomain
