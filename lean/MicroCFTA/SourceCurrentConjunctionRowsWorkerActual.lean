import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability
import MicroCFTA.SourceCurrentAllocatedProbeConjunction

/-!
# Actual graphs and physical receipts of current row workers

Literal successful reads derive their graphs and exact operation caches.
Requirements need equal arities. The whole row worker derives that fact
from its actual matching tuple list and adds no source arity check.
Initial physical facts also derive finite worker execution and its effects.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsWorkerActual
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker
open SourceCurrentConjunctionRowsWorkerStability (bind_done_iff)
open SourceCurrentConjunctionRowsWorkerCompletion (StableRun)
namespace Read
export SourceCurrentConjunctionCompletionReads (Exposures Projections)
end Read
namespace Req
export SourceCurrentConjunctionRequirements (ClassRequirements Requirements SameArity)
end Req
namespace Alloc
export SourceCurrentConjunctionRowsAllocation (Tuple Tuples Rows Ready Effects RowsReady)
end Alloc
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Successful exposures retain their literal read graph and unchanged equality operations. -/
theorem exposures_graph [DecidableEq (EdgeKey Symbol Guard)]
    {h : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {edges : List (List (EdgeValue Symbol Guard))} (done : exposures h nodes before = .done edges after) :
    Read.Exposures nodes before.heap edges after.heap ∧ after.equality = before.equality := by
  induction nodes generalizing before edges after with
  | nil => cases done; exact ⟨.nil, rfl⟩
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges h value before.heap with
      | done own heap =>
          simp only [exposures, read] at done
          obtain ⟨rest, final, restDone, returned⟩ := (bind_done_iff _ _ edges after).mp done
          obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
          have tail := ih restDone
          exact ⟨.cons (.done h read) tail.1, tail.2⟩
      | pending | unresolved | exhausted => simp only [exposures, read] at done; cases done

/-- Successful projection jobs derive their exact source order and unchanged equality cache. -/
theorem projections_graph [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {jobs : List (Job Symbol Formula)} {before after : Physical Symbol Formula}
    {values : List (Value Symbol Guard)} (done : projections p h jobs before = .done values after) :
    Read.Projections jobs before.heap values after.heap ∧ after.equality = before.equality := by
  induction jobs generalizing before values after with
  | nil => cases done; exact ⟨.nil, rfl⟩
  | cons job jobs ih =>
      obtain ⟨forest, path⟩ := job
      cases projected : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
      | done value heap =>
          simp only [projections, projected] at done
          obtain ⟨rest, final, restDone, returned⟩ := (bind_done_iff _ _ values after).mp done
          obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
          have tail := ih restDone
          exact ⟨.cons (SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ projected) tail.1, tail.2⟩
      | pending | unresolved | exhausted => simp only [projections, projected] at done; cases done

/-- Successful class jobs retain canonical rows and the same operation cache. -/
theorem classes_graph [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {forests : List (List (Value Symbol Guard))} {constraints : EqualityNormalize.Constraints}
    {before after : Physical Symbol Formula} {rows : List (List (Value Symbol Guard))}
    (done : classes p h forests constraints before = .done rows after) :
    Req.ClassRequirements forests constraints before.heap rows after.heap ∧ after.equality = before.equality := by
  induction constraints generalizing before rows after with
  | nil => cases done; exact ⟨.nil, rfl⟩
  | cons paths constraints ih =>
      obtain ⟨projected, middle, first, later⟩ := (bind_done_iff _ _ rows after).mp done
      obtain ⟨rest, final, second, returned⟩ := (bind_done_iff _ _ rows after).mp later
      obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
      have head := projections_graph first
      have tail := ih second
      exact ⟨.cons head.1 tail.1, tail.2.trans head.2⟩

/-- Requirements graph reconstruction consumes arity evidence without inventing a worker check. -/
theorem requirements_graph [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {edges : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : Physical Symbol Formula} {rows : List (List (Value Symbol Guard))}
    (same : Req.SameArity edges) (done : requirements p h edges constraints before = .done rows after) :
    Req.Requirements edges constraints before.heap rows after.heap ∧ after.equality = before.equality := by
  obtain ⟨rest, final, first, returned⟩ := (bind_done_iff _ _ rows after).mp done
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
  have actual := classes_graph first
  exact ⟨.run same actual.1, actual.2⟩

/-- A successful tuple derives its actual accessor allocation and contradiction or live requirements. -/
theorem tuple_graph [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {edges : List (EdgeValue Symbol Guard)} {before after : Physical Symbol Formula}
    {row : Option (List (List (Value Symbol Guard)))}
    (same : Req.SameArity edges) (done : tuple p h edges before = .done row after) : Alloc.Tuple edges before row after := by
  cases folded : (SourceCurrentConjunctionEquality.fold edges before.equality).1 with
  | error => simp only [tuple, folded] at done; cases done
  | ok value =>
      cases value with
      | none => simp only [tuple, folded] at done; cases done
      | some result =>
          cases constraints : SourceEqualityInheritedPayload.classes result.payload with
          | none =>
              simp only [tuple, folded, constraints] at done
              cases done
              exact .contradiction folded constraints
          | some constraints =>
              simp only [tuple, folded, constraints] at done
              obtain ⟨rows, final, completed, returned⟩ := (bind_done_iff _ _ row after).mp done
              obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
              have actual := requirements_graph same completed
              have stateEq : (⟨final.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩ : Physical Symbol Formula) = final :=
                congrArg (fun operations => (⟨final.heap, operations⟩ : Physical Symbol Formula)) actual.2.symm
              simpa only [stateEq] using (_root_.MicroCFTA.SourceCurrentConjunctionRowsAllocation.Tuple.live folded constraints actual.1)

/-- A successful tuple list retains literal filtering order and every allocation state. -/
theorem tuples_graph [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {inputs : List (List (EdgeValue Symbol Guard))} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))}
    (same : ∀ tuple ∈ inputs, Req.SameArity tuple)
    (done : tuples p h inputs before = .done rows after) : Alloc.Tuples inputs before rows after := by
  induction inputs generalizing before rows after with
  | nil => cases done; exact .nil
  | cons edges inputs ih =>
      obtain ⟨row, middle, first, later⟩ := (bind_done_iff _ _ rows after).mp done
      obtain ⟨rest, final, second, returned⟩ := (bind_done_iff _ _ rows after).mp later
      have firstGraph := tuple_graph (same _ List.mem_cons_self) first
      have restGraph := ih (fun tuple member => same tuple (List.mem_cons_of_mem _ member)) second
      cases row with
      | none =>
          obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
          exact .skip firstGraph restGraph
      | some row =>
          obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
          exact .keep firstGraph restGraph

/-- The whole source worker derives equal arities from its actual matching tuple filter. -/
theorem rows_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))}
    (done : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows after) : Alloc.Rows nodes before rows after := by
  obtain ⟨edges, middle, exposed, allocated⟩ := (bind_done_iff _ _ rows after).mp done
  have reads := exposures_graph exposed
  have actual := tuples_graph (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
    (SourceCurrentConjunctionTuples.tuples_matching edges tuple member)) allocated
  apply _root_.MicroCFTA.SourceCurrentConjunctionRowsAllocation.Rows.run reads.1
  simpa only [← reads.2] using actual

/-- Legitimate initial physical facts construct finite literal rows and their same-state effects. -/
theorem rows_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : List (Value Symbol Guard)) (before : Physical Symbol Formula) (ready : Alloc.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (probes : ProbeHeap before.heap) :
    ∃ rows after, Alloc.Rows nodes before rows after ∧ Alloc.Effects before after ∧ Alloc.RowsReady after rows ∧
      ProbeHeap after.heap ∧ StableRun (fun p h => SourceCurrentConjunctionRowsWorker.rows p h nodes before) rows after := by
  obtain ⟨rows, after, actual, effects, rowsReady⟩ := SourceCurrentConjunctionRowsAllocation.rows_complete nodes before ready available closed
  exact ⟨rows, after, actual, effects, rowsReady,
    SourceCurrentAllocatedProbeConjunction.rows_heap actual ready available closed probes,
    SourceCurrentConjunctionRowsWorkerCompletion.rows_complete actual⟩

/-- Initial invariants attach the derived physical receipt to the exact supplied successful return. -/
theorem rows_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (ready : Alloc.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (probes : ProbeHeap before.heap)
    (done : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows after) :
    Alloc.Rows nodes before rows after ∧ Alloc.Effects before after ∧ Alloc.RowsReady after rows ∧ ProbeHeap after.heap := by
  obtain ⟨candidate, reached, actual, effects, rowsReady, afterProbes, stable⟩ := rows_finite nodes before ready available closed probes
  obtain ⟨a, b, returns⟩ := stable
  obtain ⟨rfl, rfl⟩ := SourceCurrentConjunctionRowsWorkerStability.rows_done_unique done
    (returns a b (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨actual, effects, rowsReady, afterProbes⟩

end MicroCFTA.SourceCurrentConjunctionRowsWorkerActual
