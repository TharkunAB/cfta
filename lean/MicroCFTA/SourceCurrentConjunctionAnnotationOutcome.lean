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
variable {Symbol Formula Output : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
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

end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section Concrete
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq (Value ConcreteSymbol ConcreteGuard)]

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
    (probes : ProbeHeap before.native.machine.heap) (available : Available before.native.machine.heap query)
    (heap : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedConjunctionWorker.call projectionFuel readFuel budget
      query before memo).state.native.machine.heap := by
  have own := call_heap annotation projectionFuel readFuel budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before) ready probes available heap
  cases observed : call projectionFuel readFuel budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done output after =>
      obtain ⟨answer, saved⟩ := output
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, HeapOutcome, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap
  | failed fault after =>
      have afterHeap : Heap annotation after.heap := by
        simpa only [observed, HeapOutcome, Outcome.state] using own
      have heapEq : (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical ConcreteSymbol FullSyntax.Formula => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [SourceCurrentAllocatedConjunctionWorker.call, observed,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq] using afterHeap

/-- Both endpoint-guard branches preserve annotations, including retained failed check states. -/
theorem enabled_check_heap {width : Nat} (annotation : ConcreteGuard → Prop)
    (projectionFuel readFuel : Nat) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Checked width) (memo : Memo) (queries : SourceEndpointMemo.Memos)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical before))
    (probes : ProbeHeap before.native.machine.heap) (available : Available before.native.machine.heap query)
    (heap : Heap annotation before.native.machine.heap) :
    Heap annotation (SourcePruningEnumerationEnabledEmpty.check projectionFuel readFuel query
      before memo queries).1.state.native.machine.heap := by
  unfold SourcePruningEnumerationEnabledEmpty.check
  dsimp only
  split
  · exact allocated_call_heap annotation projectionFuel readFuel 1000 query before memo ready probes available heap
  · exact heap

end Concrete
end MicroCFTA.SourceCurrentConjunctionAnnotationOutcome
