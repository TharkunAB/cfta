import MicroCFTA.SourceCurrentConjunctionTupleAnnotationOutcome
import MicroCFTA.SourceCurrentConjunctionDemandAnnotations
import MicroCFTA.SourceCurrentConjunctionDemandEffects
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome
import MicroCFTA.SourcePruningEnumerationEnabledEmpty

/-!
# Annotation heaps through enabled emptiness checks

Initial physical readiness, stored probes, and available inputs supply
each reached operation. Every failed check retains its reached heap.
-/
namespace MicroCFTA.SourceCurrentConjunctionAnnotationOutcome
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula Output : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Completed and failed worklists retain annotations at their actual heap. -/
def HeapOutcome (annotation : Guard → Prop) (result : Outcome Symbol Formula Output) : Prop :=
  Heap annotation result.state.heap

private theorem bind_heap {Input Output : Type} (annotation : Guard → Prop)
    (first : Outcome Symbol Formula Input)
    (next : Input → Physical Symbol Formula → Outcome Symbol Formula Output)
    (safe : HeapOutcome annotation first)
    (continued : ∀ value after, first = .done value after → HeapOutcome annotation (next value after)) :
    HeapOutcome annotation (first.bind next) := by
  cases first with
  | done value after => exact continued value after rfl
  | failed => exact safe

private theorem map_heap {Input Output : Type} (annotation : Guard → Prop)
    (first : Outcome Symbol Formula Input) (convert : Input → Output)
    (safe : HeapOutcome annotation first) :
    HeapOutcome annotation (first.bind fun value after => .done (convert value) after) := by
  cases first <;> exact safe

section Generic
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every finite worklist observation retains its original annotation predicate. -/
theorem explore_heap (annotation : Guard → Prop) (projectionFuel readFuel budget : Nat)
    (table : Table Symbol Formula) (pending : List (List (Value Symbol Guard)))
    (before : Physical Symbol Formula) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (probes : ProbeHeap before.heap)
    (available : ∀ nodes ∈ pending, Values before.heap nodes) (heap : Heap annotation before.heap) :
    HeapOutcome annotation (explore projectionFuel readFuel budget table pending before) := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          rw [explore]
          exact heap
      | cons nodes rest ih =>
          have restAvailable : ∀ nodes ∈ rest, Values before.heap nodes :=
            fun nodes member => available nodes (List.mem_cons_of_mem _ member)
          rw [explore]
          split
          · exact ih table before ready probes restAvailable heap
          · split
            · exact ih table before ready probes restAvailable heap
            · rename_i admitted
              have entered := SourceCurrentConjunctionEmptinessTable.admitted
                SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed
                budget table nodes (Bool.eq_false_iff.mpr admitted)
              have closed := SourceCurrentConjunctionWorklist.closed_values nodes entered.2.1
              have rowSafe := SourceCurrentConjunctionRowsAnnotationOutcome.rows_heap annotation
                projectionFuel readFuel nodes before ready (available nodes List.mem_cons_self) closed heap
              cases observed : SourceCurrentConjunctionRowsWorker.rows projectionFuel readFuel nodes before with
              | done requirements middle =>
                  have checked := SourceCurrentConjunctionRowsWorkerActual.rows_verified ready
                    (available nodes List.mem_cons_self) closed probes observed
                  obtain ⟨_, effects, rowsReady, middleProbes⟩ := checked
                  have middleHeap : Heap annotation middle.heap := by
                    simpa only [observed, SourceCurrentConjunctionRowsAnnotationOutcome.HeapOutcome,
                      SourceCurrentConjunctionRowsWorker.Outcome.state] using rowSafe
                  have pendingReady : ∀ next ∈ requirements.flatten ++ rest, Values middle.heap next := by
                    intro next member
                    rcases List.mem_append.mp member with generated | original
                    · obtain ⟨row, included, present⟩ := List.mem_flatten.mp generated
                      exact (rowsReady row included next present).1
                    · intro value included
                      exact effects.keeps.available value (restAvailable next original value included)
                  change HeapOutcome annotation
                    (explore projectionFuel readFuel (budget - 1) (⟨nodes, requirements⟩ :: table)
                      (requirements.flatten ++ rest) middle)
                  exact smaller (budget - 1) (by omega) _ _ middle effects.ready
                    middleProbes pendingReady middleHeap
              | failed fault after =>
                  change Heap annotation after.heap
                  simpa only [observed, SourceCurrentConjunctionRowsAnnotationOutcome.HeapOutcome,
                    SourceCurrentConjunctionRowsWorker.Outcome.state] using rowSafe

/-- Open starts return directly. Every entered closed worklist preserves annotations. -/
theorem decision_heap [DecidableEq (Value Symbol Guard)]
    (annotation : Guard → Prop) (projectionFuel readFuel budget : Nat) (start : Value Symbol Guard)
    (before : Physical Symbol Formula) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (probes : ProbeHeap before.heap) (available : Available before.heap start)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (decision projectionFuel readFuel budget start before) := by
  unfold decision
  split
  · have first := explore_heap annotation projectionFuel readFuel budget [] [[start]] before ready probes
      (by
        intro nodes member value included
        have nodesEq : nodes = [start] := by simpa only [List.mem_singleton] using member
        subst nodes
        have valueEq : value = start := by simpa only [List.mem_singleton] using included
        simpa only [valueEq] using available) heap
    apply bind_heap annotation _ _ first
    intro table after observed
    have afterHeap : Heap annotation after.heap := by
      simpa only [observed, HeapOutcome, Outcome.state] using first
    split <;> exact afterHeap
  · exact heap

/-- Each reached worklist branch derives preservation from the original annotation heap. -/
private theorem demand_explore_heap (annotation : Guard → Prop) (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula) (ready : Ready before)
    (available : ∀ nodes ∈ pending, Values before.heap nodes) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionDemandWorker.explore p h budget table pending before).state.heap := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil => simpa only [SourceCurrentConjunctionDemandWorker.explore, Outcome.state] using heap
      | cons nodes rest tail =>
          rw [SourceCurrentConjunctionDemandWorker.explore.eq_def]
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
                  (SourceCurrentConjunctionDemandAdmission.run p h budget nodes before).state :=
                Eq.mp (by congr <;> exact Subsingleton.elim _ _)
                  (SourceCurrentConjunctionDemandEffects.run_effects p h budget nodes before ready inputs)
              have annotated := SourceCurrentConjunctionDemandAnnotations.run_annotation_heap annotation p h budget nodes before ready inputs noFree heap
              cases actual : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before with
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
                      have charge := SourceCurrentConjunctionDemandAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements actual
                      have returned := (SourceCurrentConjunctionDemandExecution.admission_graph actual).verified
                        ready inputs noFree
                      have remaining : ∀ group ∈ requirements.flatten ++ rest, Values middle.heap group := by
                        intro group member
                        rcases List.mem_append.mp member with fresh | old
                        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                          exact (returned.2 row rowIn group groupIn).1
                        · exact oldInputs group old
                      exact smaller (budget - (predecessor + 1)) (by omega)
                        (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready remaining middleHeap

/-- The open shortcut and every fixed-point outcome retain the original annotation predicate. -/
private theorem demand_decision_heap [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (annotation : Guard → Prop) (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap query) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionDemandWorker.decision p h budget query before).state.heap := by
  unfold SourceCurrentConjunctionDemandWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes := by
      intro nodes member
      cases List.mem_singleton.mp member
      intro value included
      cases List.mem_singleton.mp included
      exact available
    have first := demand_explore_heap annotation p h budget [] [[query]] before ready inputs heap
    cases actual : SourceCurrentConjunctionDemandWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact heap

end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section Concrete
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq (Value ConcreteSymbol ConcreteGuard)]

private theorem demand_call_heap (annotation : ConcreteGuard → Prop)
    (projectionFuel readFuel budget : Nat) (memo : Memo) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (ready : Ready before)
    (available : Available before.heap query) (heap : Heap annotation before.heap) :
    Heap annotation (SourceCurrentConjunctionDemandWorker.call projectionFuel readFuel budget memo query before).state.heap := by
  unfold SourceCurrentConjunctionDemandWorker.call
  split
  · exact heap
  · have first := demand_decision_heap annotation projectionFuel readFuel budget query before ready available heap
    cases actual : SourceCurrentConjunctionDemandWorker.decision projectionFuel readFuel budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first

/-- Memo hits and every actual memo-miss outcome retain the same annotation predicate. -/
theorem call_heap (annotation : ConcreteGuard → Prop) (projectionFuel readFuel budget : Nat)
    (memo : Memo) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Physical ConcreteSymbol FullSyntax.Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (probes : ProbeHeap before.heap)
    (available : Available before.heap query) (heap : Heap annotation before.heap) :
    HeapOutcome annotation (call projectionFuel readFuel budget memo query before) := by
  cases observed : memo query.referenceOf with
  | none =>
      simp only [call, observed]
      exact map_heap annotation _ _
        (decision_heap annotation projectionFuel readFuel budget query before ready probes available heap)
  | some entry =>
      obtain ⟨stored, answer⟩ := entry
      simpa only [call, observed, HeapOutcome, Outcome.state] using heap

/-- Physical advancement retains the heap of every successful or failed raw call. -/
theorem allocated_call_heap {width : Nat} (annotation : ConcreteGuard → Prop)
    (projectionFuel readFuel budget : Nat) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical before))
    (_probes : ProbeHeap before.native.machine.heap) (available : Available before.native.machine.heap query)
    (heap : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedConjunctionWorker.call projectionFuel readFuel budget
      query before memo).state.native.machine.heap := by
  have own := demand_call_heap annotation projectionFuel readFuel budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before) ready available heap
  cases observed : SourceCurrentConjunctionDemandWorker.call projectionFuel readFuel budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done output after =>
      obtain ⟨answer, saved⟩ := output
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap
  | failed fault after =>
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap

/-- Physical advancement retains the heap of every successful or failed raw call. -/
theorem allocated_tuple_call_heap {width : Nat} (annotation : ConcreteGuard → Prop)
    (projectionFuel readFuel budget : Nat) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical before))
    (available : Available before.native.machine.heap query)
    (heap : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedTupleConjunctionWorker.call projectionFuel readFuel budget
      query before memo).state.native.machine.heap := by
  have own := demand_call_heap annotation projectionFuel readFuel budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before) ready available heap
  cases observed : SourceCurrentConjunctionDemandWorker.call projectionFuel readFuel budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done output after =>
      obtain ⟨answer, saved⟩ := output
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedTupleConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap
  | failed fault after =>
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedTupleConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap

/-- Both endpoint-guard branches preserve annotations, including retained failed check states. -/
theorem enabled_check_heap {width : Nat} (annotation : ConcreteGuard → Prop)
    (projectionFuel readFuel : Nat) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Checked width) (memo : Memo) (queries : SourceEndpointMemo.Memos)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical before))
    (_probes : ProbeHeap before.native.machine.heap) (available : Available before.native.machine.heap query)
    (heap : Heap annotation before.native.machine.heap) :
    Heap annotation (SourcePruningEnumerationEnabledEmpty.check projectionFuel readFuel query
      before memo queries).1.state.native.machine.heap := by
  unfold SourcePruningEnumerationEnabledEmpty.check
  dsimp only
  split
  · exact allocated_tuple_call_heap annotation projectionFuel readFuel
      SourceCurrentConjunctionTupleBudget.currentTupleBudget query before memo ready available heap
  · exact heap

end Concrete
end MicroCFTA.SourceCurrentConjunctionAnnotationOutcome
