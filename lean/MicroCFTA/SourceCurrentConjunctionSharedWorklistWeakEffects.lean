import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
import MicroCFTA.SourceCurrentConjunctionRequirementCellsWeakEffects
import MicroCFTA.SourceCurrentConjunctionRequirementRowsWeakValues
import MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
import MicroCFTA.SourceCurrentConjunctionTuplePullWeakEffects

/-!
# Weak physical effects through actual shared work

Current cells and raw tuples retain resident closed operands. Pending node
queries need only residency. Admission derives their closedness before an
actual sample. Deferred forcing and row preparation retain these facts at
each returned state. The finite run preserves semantic heaps, coverage,
records, and issued identities on successful and failed outcomes.
No equality validity, cost heap, or future execution is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistWeakEffects
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionSharedWorklistStep
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

private structure HeapEffects (before after : Physical) : Prop where
  semantic : SemanticHeap after.heap
  covered : Covered [] after.heap
  growth : Grows before.heap after.heap
  history : Extends before.heap.nodes.issued after.heap.nodes.issued

private theorem HeapEffects.refl (before : Physical) (semantic : SemanticHeap before.heap)
    (covered : Covered [] before.heap) : HeapEffects before before :=
  ⟨semantic, covered, grows_refl _, extends_refl _⟩

private theorem HeapEffects.trans {before middle after : Physical}
    (first : HeapEffects before middle) (last : HeapEffects middle after) : HeapEffects before after :=
  ⟨last.semantic, last.covered, grows_trans first.growth last.growth, extends_trans first.history last.history⟩

private structure Invariant (before : WorkState) : Prop where
  cells : SourceCurrentConjunctionRequirementCellsValues.Invariant before.storage.requirements
  cellClosed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before.storage.requirements
  raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs before.storage
  rawClosed : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed before.storage
  pending : ∀ nodes, Task.nodes nodes ∈ before.pending → Values before.storage.requirements.physical.heap nodes
  table : ∀ entry ∈ before.table, Values before.storage.requirements.physical.heap entry.nodes

private theorem values_grows {before after : Physical} (kept : HeapEffects before after)
    (nodes : List Node) (available : Values before.heap nodes) : Values after.heap nodes :=
  fun node member => (available node member).grows before.heap after.heap kept.growth kept.history

private theorem cells_grows (before : Cells) (after : Physical)
    (kept : HeapEffects before.physical after)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before) :
    SourceCurrentConjunctionRequirementCellsValues.Invariant {before with physical := after} := by
  intro handle cell found
  have own := values handle cell found
  cases cell with
  | column nodes | done nodes => exact values_grows kept nodes own
  | pending cursor =>
      exact ⟨values_grows kept cursor.collected own.1,
        fun job member => values_grows kept job.1 (own.2 job member)⟩

private theorem raw_grows (before after : Storage)
    (kept : HeapEffects before.requirements.physical after.requirements.physical)
    (same : after.spines = before.spines)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs before) :
    SourceCurrentConjunctionRequirementRowsEffects.SpineInputs after := by
  intro spine member
  rw [same] at member
  have own := raw spine member
  cases spine with
  | done row => trivial
  | pending tuples =>
      exact fun tuple included row present => InternedEdgeResidency.edge_grows _ _ kept.growth row (own tuple included row present)

private theorem storage_inputs (before : WorkState) (storage : Storage) (prior : Invariant before)
    (kept : HeapEffects before.storage.requirements.physical storage.requirements.physical)
    (cells : SourceCurrentConjunctionRequirementCellsValues.Invariant storage.requirements)
    (cellClosed : SourceCurrentConjunctionRequirementCellsClosed.Invariant storage.requirements)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage)
    (rawClosed : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed storage) :
    Invariant {before with storage := storage} :=
  ⟨cells, cellClosed, raw, rawClosed,
    fun nodes member => values_grows kept nodes (prior.pending nodes member),
    fun entry member => values_grows kept entry.nodes (prior.table entry member)⟩

private theorem physical_inputs (before : WorkState) (after : Physical) (prior : Invariant before)
    (kept : HeapEffects before.storage.requirements.physical after) : Invariant (withPhysical before after) :=
  storage_inputs before (withPhysical before after).storage prior kept
    (cells_grows before.storage.requirements after kept prior.cells) prior.cellClosed
    (raw_grows before.storage (withPhysical before after).storage kept rfl prior.raw) prior.rawClosed

private theorem allocate_raw (tuples : List (List Row)) (storage : Storage)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage)
    (rawClosed : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed storage)
    (resident : ∀ tuple ∈ tuples, Edges storage.requirements.physical.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) :
    SourceCurrentConjunctionRequirementRowsEffects.SpineInputs
        (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) storage).2 ∧
      SourceCurrentConjunctionRequirementRowsClosed.SpineClosed
        (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) storage).2 := by
  constructor
  · intro spine member
    rcases List.mem_append.mp member with old | fresh
    · exact raw spine old
    · cases List.mem_singleton.mp fresh
      exact resident
  · intro spine member
    rcases List.mem_append.mp member with old | fresh
    · exact rawClosed spine old
    · cases List.mem_singleton.mp fresh
      exact closed

private theorem initial_inputs (budget : Nat) (start : Node) (before : Physical)
    (available : Available before.heap start) : Invariant (initial budget start before) := by
  refine ⟨SourceCurrentConjunctionRequirementCellsValues.initial_values before,
    SourceCurrentConjunctionRequirementCellsClosed.initial_closed before, ?_, ?_, ?_, ?_⟩
  · intro spine member
    cases member
  · intro spine member
    cases member
  · intro nodes member
    have same : nodes = [start] := Task.nodes.inj (List.mem_singleton.mp member)
    subst nodes
    intro node included
    cases List.mem_singleton.mp included
    exact available
  · intro entry member
    cases member

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_effects (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (semantic : SemanticHeap before.storage.requirements.physical.heap)
    (covered : Covered [] before.storage.requirements.physical.heap)
    (prior : Invariant {before with pending := .nodes nodes :: rest}) :
    HeapEffects before.storage.requirements.physical (visit h nodes rest before).state.storage.requirements.physical ∧
      Invariant (visit h nodes rest before).state := by
  have tail : ∀ query, Task.nodes query ∈ rest → Values before.storage.requirements.physical.heap query :=
    fun query member => prior.pending query (List.mem_cons_of_mem _ member)
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨HeapEffects.refl _ semantic covered,
        ⟨prior.cells, prior.cellClosed, prior.raw, prior.rawClosed, tail, prior.table⟩⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨HeapEffects.refl _ semantic covered,
            ⟨prior.cells, prior.cellClosed, prior.raw, prior.rawClosed, tail, prior.table⟩⟩
      | false =>
          have admitted := SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
            SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes skipped
          have queryClosed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
          have available := prior.pending nodes List.mem_cons_self
          have first := SourceCurrentConjunctionTuplePullWeakEffects.sample_effects h before.budget nodes
            before.storage.requirements.physical semantic covered available queryClosed
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              have kept : HeapEffects before.storage.requirements.physical physical := by
                refine ⟨?_, ?_, ?_, ?_⟩
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.2.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.2.2.1
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact ⟨kept, physical_inputs {before with pending := .nodes nodes :: rest} physical prior kept⟩
          | done result physical =>
              have kept : HeapEffects before.storage.requirements.physical physical := by
                refine ⟨?_, ?_, ?_, ?_⟩
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.2.1
                · simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.2.2.2.1
              have current := physical_inputs {before with pending := .nodes nodes :: rest} physical prior kept
              have remaining : ∀ query, Task.nodes query ∈ rest → Values physical.heap query :=
                fun query member => values_grows kept query (tail query member)
              have queryValues : Values physical.heap nodes := values_grows kept nodes available
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨kept, ⟨current.cells, current.cellClosed, current.raw, current.rawClosed, remaining, current.table⟩⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      refine ⟨kept, ⟨current.cells, current.cellClosed, current.raw, current.rawClosed, remaining, ?_⟩⟩
                      intro entry member
                      rcases List.mem_cons.mp member with same | old
                      · cases same
                        exact queryValues
                      · exact current.table entry old
                  | cons tuple tuples =>
                      have returned := SourceCurrentConjunctionTuplePullWeakEffects.sample_fit h before.budget nodes
                        before.storage.requirements.physical physical (tuple :: tuples) sampled semantic covered available queryClosed
                      have allocated := allocate_raw (tuple :: tuples) (withPhysical before physical).storage
                        current.raw current.rawClosed (fun tuple member => (returned tuple member).1)
                        (fun tuple member => (returned tuple member).2)
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨kept, ⟨current.cells, current.cellClosed, allocated.1, allocated.2, ?_, ?_⟩⟩
                      · intro query member
                        rcases List.mem_cons.mp member with impossible | old
                        · cases impossible
                        · exact remaining query old
                      · intro entry member
                        rcases List.mem_cons.mp member with same | old
                        · cases same
                          exact queryValues
                        · exact current.table entry old

private theorem step_effects (p h : Nat) (before : WorkState)
    (semantic : SemanticHeap before.storage.requirements.physical.heap)
    (covered : Covered [] before.storage.requirements.physical.heap) (prior : Invariant before) :
    HeapEffects before.storage.requirements.physical (step p h before).state.storage.requirements.physical ∧
      Invariant (step p h before).state := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact ⟨HeapEffects.refl _ semantic covered, prior⟩
  | cons task rest =>
      have tail : ∀ nodes, Task.nodes nodes ∈ rest → Values before.storage.requirements.physical.heap nodes := by
        intro nodes member
        apply prior.pending nodes
        rw [pending]
        exact List.mem_cons_of_mem _ member
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_effects h nodes rest before semantic covered
          rw [← pending]
          exact prior
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨HeapEffects.refl _ semantic covered,
                ⟨prior.cells, prior.cellClosed, prior.raw, prior.rawClosed, tail, prior.table⟩⟩
          | cons handle handles =>
              have first := SourceCurrentConjunctionRequirementCellsWeakEffects.force_effects p h handle
                before.storage.requirements semantic covered prior.cells prior.cellClosed
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [forced] at first
                  have kept : HeapEffects before.storage.requirements.physical cells.physical :=
                    ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1⟩
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact ⟨kept, storage_inputs before _ prior kept first.2.2.2.2.1 first.2.2.2.2.2.1
                    (raw_grows before.storage _ kept rfl prior.raw) prior.rawClosed⟩
              | done nodes cells =>
                  rw [forced] at first
                  have kept : HeapEffects before.storage.requirements.physical cells.physical :=
                    ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1⟩
                  have current := storage_inputs before {before.storage with requirements := cells} prior kept
                    first.2.2.2.2.1 first.2.2.2.2.2.1
                    (raw_grows before.storage _ kept rfl prior.raw) prior.rawClosed
                  have returned := first.2.2.2.2.2.2 nodes cells rfl
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  have next : Invariant
                      {{before with storage := {before.storage with requirements := cells}} with
                        pending := .nodes nodes :: .requirements handles :: rest} := by
                    refine ⟨current.cells, current.cellClosed, current.raw, current.rawClosed, ?_, current.table⟩
                    intro query member
                    rcases List.mem_cons.mp member with same | member
                    · have equal : query = nodes := Task.nodes.inj same
                      subst query
                      exact returned.1
                    · rcases List.mem_cons.mp member with impossible | old
                      · cases impossible
                      · exact values_grows kept query (tail query old)
                  have last := visit_effects h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} kept.semantic kept.covered next
                  exact ⟨kept.trans last.1, last.2⟩
      | rows handle =>
          have first := SourceCurrentConjunctionRequirementRowsWeakValues.nextRow_values handle before.storage
            semantic prior.cells prior.raw
          have closure := SourceCurrentConjunctionRequirementRowsClosed.nextRow_closed handle before.storage
            prior.cellClosed prior.rawClosed
          have heapSame := SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap handle before.storage
          have kept : HeapEffects before.storage.requirements.physical
              (SourceCurrentConjunctionRequirementRows.nextRow handle before.storage).state.requirements.physical := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [heapSame]
              exact semantic
            · rw [heapSame]
              exact covered
            · rw [heapSame]
              exact grows_refl _
            · rw [heapSame]
              exact extends_refl _
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [advanced] at first closure kept
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨kept, storage_inputs before storage prior kept first.1 closure.1 first.2 closure.2⟩
          | done row storage =>
              rw [advanced] at first closure kept
              have current := storage_inputs before storage prior kept first.1 closure.1 first.2 closure.2
              have remaining : ∀ nodes, Task.nodes nodes ∈ rest → Values storage.requirements.physical.heap nodes :=
                fun nodes member => values_grows kept nodes (tail nodes member)
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨kept, ⟨current.cells, current.cellClosed, current.raw, current.rawClosed, remaining, current.table⟩⟩
              | some row =>
                  rcases row with ⟨handles, tailHandle⟩
                  rw [step_rows_live p h handle tailHandle before rest handles storage pending advanced]
                  refine ⟨kept, ⟨current.cells, current.cellClosed, current.raw, current.rawClosed, ?_, current.table⟩⟩
                  intro nodes member
                  rcases List.mem_cons.mp member with impossible | member
                  · cases impossible
                  · rcases List.mem_cons.mp member with impossible | old
                    · cases impossible
                    · exact remaining nodes old

private theorem run_effects {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (semantic : SemanticHeap before.storage.requirements.physical.heap)
    (covered : Covered [] before.storage.requirements.physical.heap) (prior : Invariant before) :
    HeapEffects before.storage.requirements.physical outcome.state.storage.requirements.physical ∧ Invariant outcome.state := by
  revert semantic covered prior
  induction actual with
  | @failed before after fault advanced =>
      intro semantic covered prior
      simpa only [advanced, Outcome.state] using step_effects p h before semantic covered prior
  | @drained before after advanced =>
      intro semantic covered prior
      simpa only [advanced, Outcome.state] using step_effects p h before semantic covered prior
  | @more before middle outcome advanced tail ih =>
      intro semantic covered prior
      have first : HeapEffects before.storage.requirements.physical middle.storage.requirements.physical ∧ Invariant middle := by
        simpa only [advanced, Outcome.state] using step_effects p h before semantic covered prior
      obtain ⟨last, final⟩ := ih first.1.semantic first.1.covered first.2
      exact ⟨first.1.trans last, final⟩

/-- Original shared exploration retains weak physical facts on every actual outcome. -/
theorem explore_effects (p h budget : Nat) (start : Node) (before : Physical)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (available : Available before.heap start) :
    let actual := SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before
    SemanticHeap actual.state.storage.requirements.physical.heap ∧ Covered [] actual.state.storage.requirements.physical.heap ∧
      Grows before.heap actual.state.storage.requirements.physical.heap ∧
      Extends before.heap.nodes.issued actual.state.storage.requirements.physical.heap.nodes.issued := by
  have reached := (run_effects (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    semantic covered (initial_inputs budget start before available)).1
  exact ⟨reached.semantic, reached.covered, reached.growth, reached.history⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistWeakEffects
