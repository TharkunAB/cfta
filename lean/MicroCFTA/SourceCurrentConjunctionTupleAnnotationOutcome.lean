import MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome
import MicroCFTA.SourceCurrentConjunctionRowsSoundness
import MicroCFTA.SourceCurrentConjunctionTupleAdmissionEffects
import MicroCFTA.SourceCurrentConjunctionTupleWorker

/-!
# Annotation heaps through every physical tuple-worker outcome

The original annotation predicate holds at every returned heap, including
failed outcomes. Closed operands are required at admission. The worklist
derives this premise from its actual closedness guard. Successful full row
graphs supply the next available operands without a probe-heap premise.
No annotation property of a future row or returned heap is supplied.
The selected caller and native lazy demand remain separate attachments.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleAnnotationOutcome
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every admission outcome retains annotations at its exact returned heap. -/
theorem admission_heap (annotation : Guard → Prop) (p h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionTupleAdmission.run p h budget nodes before).state.heap := by
  have first := SourceCurrentConjunctionRowsAnnotationOutcome.exposures_heap annotation h nodes before
    ready.semantic ready.costs available closed heap
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed =>
      simpa only [SourceCurrentConjunctionTupleAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind,
        SourceCurrentConjunctionRowsWorker.Outcome.state,
        SourceCurrentConjunctionRowsAnnotationOutcome.HeapOutcome] using first
  | done edges exposed =>
      have actual := SourceCurrentConjunctionRowsWorkerActual.exposures_graph read
      have checked := SourceCurrentConjunctionCompletionReads.Exposures.verified
        (SourceCurrentConjunctionEquality.FieldAvailable before.equality) actual.1
        ready.semantic ready.costs ready.fields available closed
      have middleReady : Ready exposed :=
        ⟨checked.1.semantic, checked.1.costs, by simpa only [actual.2] using ready.valid,
          by simpa only [SourceCurrentConjunctionEquality.Fields, actual.2] using checked.1.annotations⟩
      have facts := SourceCurrentConjunctionTuples.tuples_verified
        (SourceCurrentConjunctionEquality.FieldAvailable before.equality) actual.1
        ready.semantic ready.costs ready.fields available closed
      have middleHeap : Heap annotation exposed.heap := by
        simpa only [read, SourceCurrentConjunctionRowsAnnotationOutcome.HeapOutcome,
          SourceCurrentConjunctionRowsWorker.Outcome.state] using first
      simp only [SourceCurrentConjunctionTupleAdmission.run, read, SourceCurrentConjunctionRowsWorker.Outcome.bind]
      by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length
      · simpa only [overflow, ↓reduceIte, SourceCurrentConjunctionRowsWorker.Outcome.state] using middleHeap
      · simp only [overflow, ↓reduceIte]
        have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
          (SourceCurrentConjunctionTuples.tuples edges) (Nat.le_of_not_gt overflow)
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil => simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using middleHeap
        | cons first rest =>
            have full : SourceCurrentConjunctionTuples.tuples edges = first :: rest := entire.symm.trans sampled
            have safe := SourceCurrentConjunctionRowsAnnotationOutcome.tuples_heap annotation p h
              (first :: rest) exposed middleReady
              (fun tuple member => (facts tuple (by simpa only [full] using member)).2.1)
              (fun tuple member => (facts tuple (by simpa only [full] using member)).2.2)
              (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
                (SourceCurrentConjunctionTuples.tuples_matching edges tuple (by simpa only [full] using member))) middleHeap
            dsimp only
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed <;>
              simpa only [processed, SourceCurrentConjunctionRowsAnnotationOutcome.HeapOutcome,
                SourceCurrentConjunctionRowsWorker.Outcome.state] using safe

/-- Each reached worklist branch derives preservation from the original annotation heap. -/
theorem explore_heap (annotation : Guard → Prop) (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula) (ready : Ready before)
    (available : ∀ nodes ∈ pending, Values before.heap nodes) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionTupleWorker.explore p h budget table pending before).state.heap := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil => simpa only [SourceCurrentConjunctionTupleWorker.explore, Outcome.state] using heap
      | cons nodes rest tail =>
          rw [SourceCurrentConjunctionTupleWorker.explore.eq_def]
          dsimp only
          split
          · exact tail table before ready (fun group member => available group (List.mem_cons_of_mem _ member)) heap
          · split
            · exact tail table before ready (fun group member => available group (List.mem_cons_of_mem _ member)) heap
            · have admitted := SourceCurrentConjunctionEmptinessTable.admitted
                SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
                (Bool.eq_false_iff.mpr (by assumption))
              have inputs := available nodes List.mem_cons_self
              have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
              have first : Effects before
                  (SourceCurrentConjunctionTupleAdmission.run p h budget nodes before).state :=
                Eq.mp (by congr <;> exact Subsingleton.elim _ _)
                  (SourceCurrentConjunctionTupleAdmissionEffects.run_effects p h budget nodes before ready inputs)
              have annotated := admission_heap annotation p h budget nodes before ready inputs noFree heap
              cases actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
              | failed fault after =>
                  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using annotated
              | done result middle =>
                  have kept : Effects before middle := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                  have middleHeap : Heap annotation middle.heap := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using annotated
                  have oldInputs : ∀ group ∈ rest, Values middle.heap group := by
                    intro group member value included
                    exact kept.keeps.available value (available group (List.mem_cons_of_mem _ member) value included)
                  cases result with
                  | overflow => exact smaller 0 admitted.1 table rest middle kept.ready oldInputs middleHeap
                  | zero => exact tail (⟨nodes, []⟩ :: table) middle kept.ready oldInputs middleHeap
                  | positive predecessor requirements =>
                      have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements actual
                      have fullRows := SourceCurrentConjunctionRowsWorkerActual.rows_graph
                        (SourceCurrentConjunctionTupleAdmission.positive_rows p h budget nodes before middle
                          predecessor requirements actual).2
                      have returned := (SourceCurrentConjunctionRowsSoundness.rows_verified fullRows ready inputs noFree).2
                      have remaining : ∀ group ∈ requirements.flatten ++ rest, Values middle.heap group := by
                        intro group member
                        rcases List.mem_append.mp member with fresh | old
                        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                          exact (returned row rowIn group groupIn).1
                        · exact oldInputs group old
                      exact smaller (budget - (predecessor + 1)) (by omega)
                        (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready remaining middleHeap

/-- The open shortcut and every fixed-point outcome retain the original annotation predicate. -/
theorem decision_heap [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (annotation : Guard → Prop) (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap query) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionTupleWorker.decision p h budget query before).state.heap := by
  unfold SourceCurrentConjunctionTupleWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes := by
      intro nodes member
      cases List.mem_singleton.mp member
      intro value included
      cases List.mem_singleton.mp included
      exact available
    have first := explore_heap annotation p h budget [] [[query]] before ready inputs heap
    cases actual : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact heap

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard

/-- Fourth-memo hits and every miss outcome retain annotations at the exact returned heap. -/
theorem call_heap [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (annotation : ConcreteGuard → Prop) (p h budget : Nat)
    (memo : SourceCurrentEmptinessMemo.Memo) (query : ConcreteNode)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (ready : Ready before)
    (available : Available before.heap query) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionTupleWorker.call p h budget memo query before).state.heap := by
  unfold SourceCurrentConjunctionTupleWorker.call
  split
  · exact heap
  · have first := decision_heap annotation p h budget query before ready available heap
    cases actual : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first

end MicroCFTA.SourceCurrentConjunctionTupleAnnotationOutcome
