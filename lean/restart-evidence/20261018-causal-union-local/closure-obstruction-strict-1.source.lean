import MicroCFTA.SourceCurrentLiteralLocalSimulation
import MicroCFTA.SourceCurrentNativeMuPublication

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ClosureLocalObstruction
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentLiteralLocalSimulation (Clauses)
open SourceCurrentDirectedClosure (Closure)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentSourceDirectedCases (Local)
open SourceCurrentOpenObservations (RowMatch)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (History)
open Productivity (Reachable)

private def Steps (ordinary recursive : Value Nat Bool) (first second : Value Nat Bool) : Prop :=
  (first = ordinary ∧ second = recursive) ∨ (first = recursive ∧ second = .empty)

private theorem child_refl (ordinary recursive : Value Nat Bool) (values : List (Value Nat Bool)) :
    All₂ (Mutual (Closure (Steps ordinary recursive))) values values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons ⟨.refl value,.refl value⟩ ih

private theorem abstract_obstruction (reader : State Nat Bool)
    (ordinaryEntry recursiveEntry : Interned NodeKey) (rows : List (EdgeValue Nat Bool))
    (depth : Nat) (free : List Reference) (depthShape ordinaryShape : Value Nat Bool)
    (successor : successors reader (.mu recursiveEntry (.node ordinaryEntry rows depth free) depthShape ordinaryShape) =
      [.node ordinaryEntry rows depth free]) (nonempty : rows ≠ []) :
    let ordinary := Value.node ordinaryEntry rows depth free
    let recursive := Value.mu recursiveEntry ordinary depthShape ordinaryShape
    (∀ first second, Steps ordinary recursive first second →
      Clauses reader (Closure (Steps ordinary recursive)) first second) ∧
    (∀ first second, Steps ordinary recursive first second →
      Local reader (Closure (Steps ordinary recursive)) first second) ∧
    ¬ Directed reader (Closure (Steps ordinary recursive)) := by
  dsimp only
  let ordinary := Value.node ordinaryEntry rows depth free
  let recursive := Value.mu recursiveEntry ordinary depthShape ordinaryShape
  have chain : Closure (Steps ordinary recursive) ordinary .empty :=
    .step (.inl ⟨rfl,rfl⟩) (.single (.inr ⟨rfl,rfl⟩))
  have reached : Reachable (successors reader) [recursive] ordinary :=
    .step (.seed List.mem_cons_self) (successor ▸ List.mem_cons_self)
  have ordinaryRows (row : EdgeValue Nat Bool) (member : row ∈ rows) :
      ∃ other, Origin reader [recursive] other ∧
        RowMatch (Mutual (Closure (Steps ordinary recursive))) row other :=
    ⟨row,⟨ordinary,reached,member⟩,rfl,rfl,child_refl ordinary recursive row.children⟩
  have epsilon (next : Value Nat Bool) (member : next ∈ successors reader recursive) :
      ∃ later, Reachable (successors reader) [.empty] later ∧
        Closure (Steps ordinary recursive) next later := by
    rw [successor] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.empty,.seed List.mem_cons_self,chain⟩
  refine ⟨?_,?_,?_⟩
  · intro first second paired
    rcases paired with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · refine ⟨?_,?_,?_⟩
      · intro name impossible; cases impossible
      · intro row found
        cases found with
        | node member => exact ordinaryRows row member
      · intro entry body shape plain impossible; cases impossible
    · refine ⟨?_,?_,?_⟩
      · intro name impossible; cases impossible
      · intro row impossible; cases impossible
      · intro entry body shape plain found
        cases found
        exact epsilon
  · intro first second paired
    rcases paired with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · refine ⟨?_,ordinaryRows,?_⟩
      · intro name impossible; cases impossible
      · intro next impossible; cases impossible
    · refine ⟨?_,?_,epsilon⟩
      · intro name impossible; cases impossible
      · intro row impossible; cases impossible
  · intro assumed
    cases rows with
    | nil => exact nonempty rfl
    | cons row rest =>
        obtain ⟨other,origin,_⟩ := (assumed ordinary .empty chain).2.1 row List.mem_cons_self
        exact MergedFreshOrdinaryGraph.origin_empty reader other origin

private def source : Syntax Nat Bool := .binder false (.node [.mk 7 true []])
private def completed := build source [] empty
private def recursive : Value Nat Bool := match completed with | .done value _ => value | .pending .. => .empty
private def reader := completed.state
private def ordinary : Value Nat Bool := match recursive with | .mu _ body _ _ => body | _ => .empty
private theorem source_done : build source [] empty = .done recursive reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source recursive reader source_done
private theorem history : History empty reader := by
  simpa only [completed,reader] using SourceCurrentNativeMuPublication.closed_history source

/-- Actual closed construction refutes unrestricted weak simulation up to transitive closure. -/
theorem checked :
    ∃ (reader : State Nat Bool) (ordinary recursive : Value Nat Bool),
      build (.binder false (.node [.mk 7 true []])) [] empty = .done recursive reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧
      (∀ first second, Steps ordinary recursive first second →
        Clauses reader (Closure (Steps ordinary recursive)) first second) ∧
      (∀ first second, Steps ordinary recursive first second →
        Local reader (Closure (Steps ordinary recursive)) first second) ∧
      ¬ Directed reader (Closure (Steps ordinary recursive)) := by
  refine ⟨reader,ordinary,recursive,source_done,ready,⟨history⟩,?_⟩
  have shape : ∃ (ordinaryEntry recursiveEntry : Interned NodeKey) (rows : List (EdgeValue Nat Bool))
      (depth : Nat) (free : List Reference) (depthShape ordinaryShape : Value Nat Bool),
      ordinary = .node ordinaryEntry rows depth free ∧
      recursive = .mu recursiveEntry ordinary depthShape ordinaryShape ∧ rows ≠ [] := by
    cbv
    exact ⟨_,_,_,_,_,_,_,rfl,rfl,by intro impossible; cases impossible⟩
  obtain ⟨ordinaryEntry,recursiveEntry,rows,depth,free,depthShape,ordinaryShape,first,second,nonempty⟩ := shape
  have successor : successors reader recursive = [ordinary] := by cbv
  rw [first] at second successor ⊢
  rw [second] at successor ⊢
  exact abstract_obstruction reader ordinaryEntry recursiveEntry rows depth free depthShape ordinaryShape successor nonempty

end MicroCFTA.ClosureLocalObstruction
