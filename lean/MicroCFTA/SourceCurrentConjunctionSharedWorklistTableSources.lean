import MicroCFTA.SourceCurrentConjunctionRequirementRowsSemantics
import MicroCFTA.SourceCurrentConjunctionTuplePullCoverage
import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed

/-!
# Table entries linked to their sampled spine sources

Each entry retains the exact source list of its shared spine. Actual fitting
sampling supplies an accepting raw tuple for every accepted query term.
The storage certificate uses the same origin and source lists throughout.
This component does not yet prove terminal semantic table coverage.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistTableSources
open Language
open InternedConstructorTemplates (Value EdgeKey EdgeValue)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

/-- Every accepted query term has a nonempty accepted tuple in this exact raw source. -/
def RawCoverage (meaning : Node → Term Symbol → Prop) (nodes : List Node) (tuples : List Tuple) : Prop :=
  ∀ term, SourceCurrentConjunctionEmptinessRows.Accepts meaning nodes term →
    ∃ tuple ∈ tuples, tuple ≠ [] ∧ ∀ edge ∈ tuple,
      SourceCurrentConjunctionEmptinessRows.EdgeAccepts meaning (SourceCurrentConjunctionEquality.edgeView edge) term

/-- A table entry uses its own sampled source at the same stable spine handle. -/
def TableCovered (meaning : Node → Term Symbol → Prop) (sources : List (List Tuple))
    (table : List (Entry Symbol Formula)) : Prop :=
  ∀ entry ∈ table, match entry.rows with
    | none => RawCoverage meaning entry.nodes []
    | some handle => ∃ tuples, sources[handle]? = some tuples ∧ RawCoverage meaning entry.nodes tuples

/-- Table coverage and cached-spine specifications use one shared metadata certificate. -/
structure Invariant (meaning : Node → Term Symbol → Prop) (origins : List Cell)
    (sources : List (List Tuple)) (before : WorkState) : Prop where
  storage : SourceCurrentConjunctionRequirementRowsSemantics.Invariant origins sources before.storage
  table : TableCovered meaning sources before.table

/-- Appending sources preserves the exact old source at every existing table handle. -/
theorem table_sources_append (meaning : Node → Term Symbol → Prop)
    (sources added : List (List Tuple)) (table : List (Entry Symbol Formula))
    (covered : TableCovered meaning sources table) : TableCovered meaning (sources ++ added) table := by
  intro entry member
  have own := covered entry member
  cases rows : entry.rows with
  | none => simpa only [rows] using own
  | some handle =>
      simp only [rows] at own
      obtain ⟨tuples, found, accepted⟩ := own
      refine ⟨tuples, ?_, accepted⟩
      rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).1)]
      exact found

/-- Literal initialization constructs the empty coupled table and storage certificate. -/
theorem initial (meaning : Node → Term Symbol → Prop) (budget : Nat) (start : Node) (before : Physical) :
    Invariant meaning [] [] (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  refine ⟨SourceCurrentConjunctionRequirementRowsSemantics.initial before, ?_⟩
  intro entry member
  cases member

/-- Existing table links survive coupled metadata extension at unchanged table contents. -/
theorem reframe {meaning : Node → Term Symbol → Prop} {origins : List Cell} {sources : List (List Tuple)}
    {before after : WorkState} (prior : Invariant meaning origins sources before)
    (addedOrigins : List Cell) (addedSources : List (List Tuple))
    (storage : SourceCurrentConjunctionRequirementRowsSemantics.Invariant
      (origins ++ addedOrigins) (sources ++ addedSources) after.storage)
    (same : after.table = before.table) :
    Invariant meaning (origins ++ addedOrigins) (sources ++ addedSources) after := by
  refine ⟨storage, ?_⟩
  rw [same]
  exact table_sources_append meaning sources addedSources before.table prior.table

private theorem physical_sources {meaning : Node → Term Symbol → Prop} {origins : List Cell}
    {sources : List (List Tuple)} (before : WorkState) (physical : Physical)
    (prior : Invariant meaning origins sources before) :
    Invariant meaning origins sources (withPhysical before physical) :=
  ⟨SourceCurrentConjunctionRequirementRowsSemantics.same_cells_spines prior.storage rfl rfl, prior.table⟩

local notation "ActualSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ActualGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ActualNode" => Value ActualSymbol ActualGuard
local notation "ActualTuple" => List (EdgeValue ActualSymbol ActualGuard)
local notation "ActualCell" => SourceCurrentConjunctionRequirementCells.Cell ActualSymbol FullSyntax.Formula
local notation "ActualState" => SourceCurrentConjunctionSharedWorklistStep.State ActualSymbol FullSyntax.Formula
local notation "ActualPhysical" => SourceCurrentConjunctionRowsWorker.Physical ActualSymbol FullSyntax.Formula
local notation "closed" => SourceCurrentConjunctionWorklist.closed
local notation "key" => (SourceCurrentConjunctionRequirements.key : ActualNode → Int)
variable [DecidableEq ActualSymbol] [DecidableEq (EdgeKey ActualSymbol ActualGuard)]

/-- The actual fitting sample supplies semantic coverage of its exact collected tuple list. -/
theorem sample_coverage (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env ActualSymbol)
    (h budget : Nat) (nodes : List ActualNode) (before after : ActualPhysical) (tuples : List ActualTuple)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) after)
    (ready : Ready before) (available : Values before.heap nodes) (closedInputs : ClosedValues nodes) :
    RawCoverage (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) nodes tuples := by
  intro term accepted
  obtain ⟨tuple, member, nonempty, _, common⟩ := SourceCurrentConjunctionTuplePullCoverage.sample_fit
    formulas solver ambient term h budget nodes before after tuples actual ready available closedInputs accepted
  exact ⟨tuple, member, nonempty, common⟩

/-- Actual admission links a new table entry to the same newly allocated sampled spine. -/
theorem visit_sources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env ActualSymbol)
    (h : Nat) (nodes : List ActualNode) (rest : List (Task ActualSymbol FullSyntax.Formula))
    (before : ActualState) (origins : List ActualCell) (sources : List (List ActualTuple))
    (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes)
    (prior : Invariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      origins sources before) :
    ∃ addedSources, Invariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      origins (sources ++ addedSources) (visit h nodes rest before).state := by
  let meaning := InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      exact ⟨prior.storage, prior.table⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget
          (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          refine ⟨[], ?_⟩
          simp only [List.append_nil]
          exact ⟨prior.storage, prior.table⟩
      | false =>
          have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed before.budget
            (queryTable before.table) nodes skipped
          have queryClosed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              refine ⟨[], ?_⟩
              simp only [List.append_nil]
              exact ⟨(physical_sources before physical prior).storage, prior.table⟩
          | done result physical =>
              have current := physical_sources before physical prior
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  refine ⟨[], ?_⟩
                  simp only [List.append_nil]
                  exact ⟨current.storage, current.table⟩
              | fit tuples =>
                  have coverage : RawCoverage meaning nodes tuples :=
                    sample_coverage formulas solver ambient h before.budget nodes
                      before.storage.requirements.physical physical tuples sampled ready available queryClosed
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      refine ⟨[], ⟨?_, ?_⟩⟩
                      · simpa only [List.append_nil, Outcome.state] using current.storage
                      · intro entry member
                        rcases List.mem_cons.mp member with same | old
                        · cases same
                          exact coverage
                        · simpa only [List.append_nil] using current.table entry old
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨[tuple :: tuples], ⟨SourceCurrentConjunctionRequirementRowsSemantics.allocate_pending
                        (tuple :: tuples) (withPhysical before physical).storage origins sources current.storage, ?_⟩⟩
                      intro entry member
                      rcases List.mem_cons.mp member with same | old
                      · cases same
                        refine ⟨tuple :: tuples, ?_, coverage⟩
                        change (sources ++ [tuple :: tuples])[before.storage.spines.length]? = some (tuple :: tuples)
                        rw [← prior.storage.length]
                        simp
                      · exact table_sources_append meaning sources [tuple :: tuples] before.table prior.table entry old

end MicroCFTA.SourceCurrentConjunctionSharedWorklistTableSources
