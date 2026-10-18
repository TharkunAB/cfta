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

private def Steps (ordinary recursive terminal : Value Nat Bool) (first second : Value Nat Bool) : Prop :=
  (first = ordinary ∧ second = recursive) ∨ (first = recursive ∧ second = terminal)

private theorem child_refl (ordinary recursive terminal : Value Nat Bool) (values : List (Value Nat Bool)) :
    All₂ (Mutual (Closure (Steps ordinary recursive terminal))) values values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons ⟨.refl value,.refl value⟩ ih

private theorem abstract_obstruction (reader : State Nat Bool)
    (ordinaryEntry recursiveEntry : Interned NodeKey) (rows : List (EdgeValue Nat Bool))
    (depth : Nat) (free : List Reference) (depthShape ordinaryShape terminal : Value Nat Bool)
    (successor : successors reader (.mu recursiveEntry (.node ordinaryEntry rows depth free) depthShape ordinaryShape) =
      [.node ordinaryEntry rows depth free]) (missing : ∃ row ∈ rows, ∀ other,
      Origin reader [terminal] other → row.entry.key.symbol ≠ other.entry.key.symbol) :
    let ordinary := Value.node ordinaryEntry rows depth free
    let recursive := Value.mu recursiveEntry ordinary depthShape ordinaryShape
    (∀ first second, Steps ordinary recursive terminal first second →
      Clauses reader (Closure (Steps ordinary recursive terminal)) first second) ∧
    (∀ first second, Steps ordinary recursive terminal first second →
      Local reader (Closure (Steps ordinary recursive terminal)) first second) ∧
    ¬ Directed reader (Closure (Steps ordinary recursive terminal)) := by
  dsimp only
  let ordinary := Value.node ordinaryEntry rows depth free
  let recursive := Value.mu recursiveEntry ordinary depthShape ordinaryShape
  have chain : Closure (Steps ordinary recursive terminal) ordinary terminal :=
    .step (.inl ⟨rfl,rfl⟩) (.single (.inr ⟨rfl,rfl⟩))
  have reached : Reachable (successors reader) [recursive] ordinary :=
    .step (.seed List.mem_cons_self) (successor ▸ List.mem_cons_self)
  have ordinaryRows (row : EdgeValue Nat Bool) (member : row ∈ rows) :
      ∃ other, Origin reader [recursive] other ∧
        RowMatch (Mutual (Closure (Steps ordinary recursive terminal))) row other :=
    ⟨row,⟨ordinary,reached,member⟩,rfl,rfl,child_refl ordinary recursive terminal row.children⟩
  have epsilon (next : Value Nat Bool) (member : next ∈ successors reader recursive) :
      ∃ later, Reachable (successors reader) [terminal] later ∧
        Closure (Steps ordinary recursive terminal) next later := by
    rw [successor] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨terminal,.seed List.mem_cons_self,chain⟩
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
    obtain ⟨row,member,absent⟩ := missing
    obtain ⟨other,origin,fields⟩ := (assumed ordinary terminal chain).2.1 row member
    exact absent other origin fields.1

private def aRow : EdgeValue Nat Bool := .mk ⟨0,⟨7,[],true⟩⟩ []
private def cRow : EdgeValue Nat Bool := .mk ⟨1,⟨8,[],true⟩⟩ []
private def ordinary : Value Nat Bool := .node ⟨0,.node [0]⟩ [aRow] 0 []
private def recursive : Value Nat Bool := .mu ⟨1,.mu ⟨.node 0,.node 0⟩⟩ ordinary ordinary ordinary
private def terminal : Value Nat Bool := .node ⟨2,.node [1]⟩ [cRow] 0 []
private def source : Syntax Nat Bool :=
  .node [.mk 0 true [.binder false (.node [.mk 7 true []]),.node [.mk 8 true []]]]
private def completed := build source [] empty
private def carrier : Value Nat Bool := match completed with | .done value _ => value | .pending .. => .empty
private def reader := completed.state
private theorem source_done : build source [] empty = .done carrier reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source carrier reader source_done
private noncomputable def history : History empty reader := by
  simpa only [completed,reader] using SourceCurrentNativeMuPublication.closed_history source

/-- A causal Ready reader and physical Empty agreement do not validate arbitrary weak simulation up to closure. -/
theorem checked :
    ∃ (reader : State Nat Bool) (carrier ordinary recursive terminal : Value Nat Bool),
      build (.node [.mk 0 true [.binder false (.node [.mk 7 true []]),.node [.mk 8 true []]]]) [] empty =
        .done carrier reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧
      Available reader ordinary ∧ Available reader recursive ∧ Available reader terminal ∧
      (∀ first second, Steps ordinary recursive terminal first second →
        (first.referenceOf == .empty) = (second.referenceOf == .empty)) ∧
      (∀ first second, Steps ordinary recursive terminal first second →
        Clauses reader (Closure (Steps ordinary recursive terminal)) first second) ∧
      (∀ first second, Steps ordinary recursive terminal first second →
        Local reader (Closure (Steps ordinary recursive terminal)) first second) ∧
      ¬ Directed reader (Closure (Steps ordinary recursive terminal)) := by
  have available : Available reader carrier :=
    (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
      (by intro value impossible; cases impossible)).result carrier reader source_done
  have recursiveMember : recursive ∈ children carrier := by cbv; exact List.mem_cons_self
  have terminalMember : terminal ∈ children carrier := by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self
  have recursiveAvailable := available.children recursive recursiveMember
  have ordinaryAvailable : Available reader ordinary :=
    recursiveAvailable.children ordinary (by cbv; exact List.mem_cons_self)
  refine ⟨reader,carrier,ordinary,recursive,terminal,source_done,ready,⟨history⟩,
    ordinaryAvailable,recursiveAvailable,available.children terminal terminalMember,?_,?_⟩
  · intro first second paired
    rcases paired with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · apply abstract_obstruction reader ⟨0,.node [0]⟩ ⟨1,.mu ⟨.node 0,.node 0⟩⟩ [aRow] 0 [] ordinary ordinary terminal
    · cbv
    · refine ⟨aRow,List.mem_cons_self,?_⟩
      intro other origin
      have member := (MergedFreshOrdinaryGraph.origin_node reader ⟨2,.node [1]⟩ [cRow] 0 [] other).mp origin
      obtain rfl := List.mem_singleton.mp member
      decide

end MicroCFTA.ClosureLocalObstruction
