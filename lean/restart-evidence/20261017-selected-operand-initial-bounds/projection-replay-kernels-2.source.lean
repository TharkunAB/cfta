import MicroCFTA.SourceCurrentProjectionNumericReplay
import MicroCFTA.SourceEqualityProjectionEffects
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.ProjectionNumericReplayIntegration
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityProjectionGraph (Project ProjectRows Forest select)
open SourceEqualityProjectionRead (Read)
open SourceEqualityProjectionUnion (ReadAll Union)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredCache (Ordinary)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionWorker (project forest readAll union rows)
open SourceEqualityRequiredWorker (Result work head)
open SourceCurrentProjectionNumericReplay
open SourceEqualityRequiredWorkerSound (bind_done work_done)

private theorem actual_readAll (reader : Nat) (values : List (Value Nat Bool))
    (before : State Nat Bool) (edges : List (EdgeValue Nat Bool)) (after : State Nat Bool)
    (done : readAll reader values before = .done edges after) :
    ∃ actual : ReadAll values before edges after, ReadAllReady reader actual := by
  induction values generalizing before edges after with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨.nil, .nil before⟩
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges reader value before with
      | done own middle =>
          simp only [readAll, read] at done
          obtain ⟨more, final, rest, returned⟩ := (bind_done _ _ edges after).mp done
          obtain ⟨rfl, rfl⟩ := Result.done.inj returned
          obtain ⟨tail, tailReady⟩ := ih middle more _ rest
          exact ⟨.cons (.done reader read) tail, .cons read tailReady⟩
      | pending | unresolved | exhausted => simp only [readAll, read] at done; cases done

private theorem actual_union (reader : Nat) (values : List (Value Nat Bool))
    (before : State Nat Bool) (result : Value Nat Bool) (after : State Nat Bool)
    (done : union reader values before = .done result after) :
    ∃ actual : Union values before result after, UnionReady reader actual := by
  obtain ⟨edges, middle, scanned, built⟩ := (bind_done _ _ result after).mp done
  obtain ⟨read, ready⟩ := actual_readAll reader values before edges middle scanned
  have completed := work_done (makeNode edges) middle result after built
  exact ⟨.node read completed, .node read completed ready⟩

private theorem actual_head (reader : Nat) (value : Value Nat Bool) (before : State Nat Bool)
    (result : Value Nat Bool) (after : State Nat Bool) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (done : head reader value before = .done result after) :
    ∃ actual : Head value before result after, HeadReady reader actual := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges reader value before with
  | done edges middle =>
      have built : run (makeNode edges) middle = (result, after) :=
        work_done _ _ _ _ (by simpa only [head, read] using done)
      have actual : Head value before result after := .read reader edges middle read built
      have ordinary := (actual.verified semantic.ready available closed).2.2.2
      exact ⟨actual, .read reader edges middle read built read ordinary⟩
  | pending | unresolved | exhausted => simp only [head, read] at done; cases done

private theorem actual_rows (reader : Nat)
    (recur : Value Nat Bool → State Nat Bool → Result Nat Bool (Value Nat Bool)) (path : List Int)
    (calls : ∀ value before result after, SemanticReady before → Available before value → value.free = [] →
      recur value before = .done result after → ∃ actual : Project path value before result after, ProjectReady reader actual)
    (index : Int) (edges : List (EdgeValue Nat Bool)) (before : State Nat Bool)
    (values : List (Value Nat Bool)) (after : State Nat Bool) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges)
    (done : rows recur index edges before = .done values after) :
    ∃ actual : ProjectRows path index edges before values after, RowsReady reader actual := by
  induction edges generalizing before values after with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨.nil, .nil path index before⟩
  | cons edge edges ih =>
      cases found : select edge.children index with
      | none =>
          obtain ⟨rest, restReady⟩ := ih before values after semantic
            (fun row member => resident row (List.mem_cons_of_mem _ member))
            (fun row member => closed row (List.mem_cons_of_mem _ member))
            (by simpa only [rows, found] using done)
          exact ⟨.missing found rest, .missing found restReady⟩
      | some child =>
          simp only [rows, found] at done
          obtain ⟨result, middle, first, later⟩ := (bind_done _ _ values after).mp done
          obtain ⟨more, final, rest, returned⟩ := (bind_done _ _ values after).mp later
          obtain ⟨rfl, rfl⟩ := Result.done.inj returned
          have member := SourceEqualityProjectionGraph.select_member found
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child member
          have childClosed := closed edge List.mem_cons_self child member
          obtain ⟨firstGraph, firstReady⟩ := calls child before result middle semantic available childClosed first
          have effects := SourceEqualityProjectionEffects.node firstGraph semantic available childClosed
          obtain ⟨restGraph, restReady⟩ := ih middle more _ effects.2.1
            (fun row member => edge_grows before middle effects.1.growth row (resident row (List.mem_cons_of_mem _ member)))
            (fun row member => closed row (List.mem_cons_of_mem _ member)) rest
          exact ⟨.selected found firstGraph restGraph, .selected found firstReady restReady⟩

private theorem actual_project (worker reader : Nat) (path : List Int) (value : Value Nat Bool)
    (before : State Nat Bool) (result : Value Nat Bool) (after : State Nat Bool)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (done : project worker reader path value before = .done result after) :
    ∃ actual : Project path value before result after, ProjectReady reader actual := by
  induction worker generalizing path value before result after with
  | zero => cases done
  | succ worker ih =>
      cases path with
      | nil =>
          obtain ⟨rfl, rfl⟩ := Result.done.inj done
          exact ⟨.root, .root value before⟩
      | cons index path =>
          cases value with
          | empty =>
              obtain ⟨rfl, rfl⟩ := Result.done.inj done
              exact ⟨.empty, .empty index path before⟩
          | reference => cases done
          | node entry edges depth free =>
              obtain ⟨values, middle, scanned, united⟩ := (bind_done _ _ result after).mp done
              have facts := semantic.ready.semantic.1.normal.facts
              obtain ⟨rowGraph, rowReady⟩ := actual_rows reader (project worker reader path) path (ih path) index edges before values middle semantic
                (resident_edges before facts.linked _ available.resident)
                (MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed) scanned
              obtain ⟨unionGraph, unionReady⟩ := actual_union reader values middle result after united
              exact ⟨.ordinary rowGraph unionGraph, .ordinary rowReady unionReady⟩
          | mu entry body depth ordinary | union entry members depth free =>
              obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
              obtain ⟨headGraph, headReady⟩ := actual_head reader _ before exposed middle semantic available closed headDone
              have headFacts := headGraph.verified semantic.ready available closed
              obtain ⟨bodyGraph, bodyReady⟩ := ih (index :: path) exposed middle result after
                (SourceEqualityRequiredSemanticCache.head headGraph semantic available closed) headFacts.2.1 headFacts.2.2.1 bodyDone
              exact ⟨.recursive True.intro headGraph bodyGraph, .recursive (headGraph := headGraph) (bodyGraph := bodyGraph) True.intro headReady bodyReady⟩

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [.var 0], .mk 1 true []])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def observed := project 12 4 [0, 0] input heap
private def output : Value Nat Bool := match observed with | .done value _ => value | _ => .empty
private def after := match observed with | .done _ state => state | _ => heap
private theorem constructed : built = .done input heap := by cbv
private theorem semantic : SemanticReady heap := SourceEqualityRequiredSemanticCache.constructed expression input heap constructed
private theorem available : Available heap input := (InternedFreshOrdinaryFacts.closed_verified expression).result input heap constructed
private theorem closed : input.free = [] := by cbv
private theorem literal : observed = .done output after := by cbv
private theorem ready : ∃ actual : Project [0, 0] input heap output after, ProjectReady 4 actual :=
  actual_project 12 4 [0, 0] input heap output after semantic available closed literal

/-- A source-built productive raw Mu replays its allocating two-step path at static worker fuel. -/
theorem productive_path (workExtra readExtra : Nat) :
    built = .done input heap ∧ (match input with | .mu .. => True | _ => False) ∧
    heap.nodes.next < after.nodes.next ∧ heap.edges.next < after.edges.next ∧
    project (5 + workExtra) (4 + readExtra) [0, 0] input heap = .done output after := by
  obtain ⟨actual, checked⟩ := ready
  exact ⟨constructed, by cbv, by cbv, by cbv, project_replay checked _ _ (by change 5 ≤ 5 + workExtra; omega) (by omega)⟩

/-- A signed selected root ignores an unrelated open reference and keeps its exact projected return. -/
theorem selected_open_forest (workExtra readExtra : Nat) :
    (Value.reference .depth : Value Nat Bool).free ≠ [] ∧
    forest (7 + workExtra) (4 + readExtra) [1, 0, 0] [.reference .depth, input] heap = .done output after ∧
    forest 0 0 [-1] [.reference .depth, input] heap = .done .empty heap := by
  obtain ⟨actual, checked⟩ := ready
  have selected : Forest [1, 0, 0] [.reference .depth, input] heap output after := .selected rfl actual
  have certified : ForestReady 4 selected := .selected rfl checked
  exact ⟨by simp [Value.free], forest_replay certified _ _ (by change 7 ≤ 7 + workExtra; omega) (by omega), rfl⟩

/-- The exact first returned heap supports a warm repeat and root union without later entry facts. -/
theorem warm_and_root_union (workExtra readExtra : Nat) :
    project (5 + workExtra) (4 + readExtra) [0, 0] input after = .done output after ∧
    forest (1 + workExtra) (4 + readExtra) [] [input] after = .done output after := by
  obtain ⟨actual, checked⟩ := ready
  have effects := SourceEqualityProjectionEffects.node actual semantic available closed
  have warmLiteral : project 12 4 [0, 0] input after = .done output after := by cbv
  obtain ⟨warm, warmReady⟩ := actual_project 12 4 [0, 0] input after output after effects.2.1
    (effects.1.available input available) closed warmLiteral
  have rootLiteral : union 4 [input] after = .done output after := by cbv
  obtain ⟨united, unionReady⟩ := actual_union 4 [input] after output after rootLiteral
  have forestReady : ForestReady 4 (Forest.root united) := .root unionReady
  exact ⟨project_replay warmReady _ _ (by change 5 ≤ 5 + workExtra; omega) (by omega),
    forest_replay forestReady _ _ (by change 1 ≤ 1 + workExtra; omega) (by omega)⟩

end MicroCFTA.ProjectionNumericReplayIntegration

#print axioms MicroCFTA.ProjectionNumericReplayIntegration.productive_path
#check @MicroCFTA.ProjectionNumericReplayIntegration.productive_path
#print axioms MicroCFTA.ProjectionNumericReplayIntegration.selected_open_forest
#check @MicroCFTA.ProjectionNumericReplayIntegration.selected_open_forest
#print axioms MicroCFTA.ProjectionNumericReplayIntegration.warm_and_root_union
#check @MicroCFTA.ProjectionNumericReplayIntegration.warm_and_root_union
