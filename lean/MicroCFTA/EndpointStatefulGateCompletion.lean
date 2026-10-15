import MicroCFTA.EndpointStatefulGateGraph
import MicroCFTA.InternedFreshOrdinaryStatefulGateCompletion

/-!
# Finite current-policy gate evaluation in returned source caches

The actual open-Mu rank and stored unfolding retain the complete cache.
Each false query passes its returned cache and both histories to the next
query. The endpoint read is a supplied pure Boolean. This module does not
claim completion or runtime adequacy for global source predicate memos.
-/
namespace MicroCFTA.EndpointStatefulGateCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome Syntax)
open InternedFreshOrdinaryGateRank (Node step fromCompleted)
open EndpointStatefulGate
open EndpointStatefulGateTrace (NodeTrace node_trace_of_done)
open InternedFreshOrdinaryStatefulGate (anyKnown child anyKnown_stable)
open InternedFreshOrdinaryStatefulGateCompletion (Completes immediate step_growth anyKnown_complete)
open InternedFreeOccurrenceRank (rank)
open EqualityNormalize

/-- Every actual stateful gate query completes, including ordered sibling effects and open nested Mu. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (path : Path) (node : Node Symbol Guard) :
    Completes node.state (fun fuel => nodeMeets unconstrained reaches fuel path node.value node.state) := by
  cases original : node.value with
  | empty => exact immediate node _ 1 false (by simp [nodeMeets, dispatch, Value.depth, Value.free])
  | reference name => exact immediate node _ 1 true (by simp [nodeMeets, dispatch])
  | union entry members depth free => exact immediate node _ 1 true (by simp [nodeMeets, dispatch])
  | mu entry body depth ordinary =>
      by_cases constrained : (!unconstrained (.mu entry body depth ordinary)) = true
      · exact immediate node _ 1 true (by simp [nodeMeets, dispatch, Value.depth, constrained])
      · by_cases closed : (Value.mu entry body depth ordinary).free.isEmpty = true
        · exact immediate node _ 1 false (by simp [nodeMeets, dispatch, Value.depth, constrained, closed])
        · have opened : (Value.mu entry body depth ordinary).free ≠ [] := by intro empty; simp [empty] at closed
          have actual := (step node).actual
          rw [original] at actual
          have smaller : rank (step node).result.value < rank node.value := by
            simpa only [original] using InternedFreshOrdinaryUnfoldRank.unfold_decreases entry body depth ordinary
              node.state node.context node.depth node.costs (original ▸ node.available) opened _ _ actual
          obtain ⟨fuel, answer, final, done, growth, history⟩ := node_complete unconstrained reaches path (step node).result
          have first := step_growth node
          exact ⟨fuel + 1, answer, final, by
              simpa [nodeMeets, dispatch, original, Value.depth, constrained, closed, actual, Outcome.bind] using done,
            grows_trans first.1 growth, extends_trans first.2 history⟩
  | node entry edges depth free =>
      by_cases finite : (depth == 0 && free.isEmpty) = true
      · exact immediate node _ 1 false (by simp only [nodeMeets, dispatch, Value.depth, Value.free, finite, ↓reduceIte])
      · cases path with
        | nil => exact immediate node _ 1 (!free.isEmpty || reaches (.node entry edges depth free)) (by simp only [nodeMeets, dispatch, Value.depth, Value.free, finite, Bool.false_eq_true, ↓reduceIte])
        | cons index rest =>
            have tests : ∀ edge ∈ edges, ∀ current : Node Symbol Guard,
                Grows node.state current.state → Extends node.state.nodes.issued current.state.nodes.issued →
                Completes current.state (fun fuel => child (nodeMeets unconstrained reaches fuel) edge.children index rest current.state) := by
              intro edge member current growth history
              cases selected : edge.children[index]? with
              | none => exact immediate current _ 0 false (by simp [child, selected])
              | some value =>
                  have available : Available node.state value := by
                    apply node.available.children value
                    rw [original]
                    exact List.mem_flatMap.mpr ⟨edge, member, List.mem_of_getElem? selected⟩
                  let next : Node Symbol Guard := { current with value := value, available := available.grows node.state current.state growth history }
                  simpa only [child, selected] using node_complete unconstrained reaches rest next
            obtain ⟨fuel, answer, final, done, growth, history⟩ := anyKnown_complete node edges
              (fun fuel edge current => child (nodeMeets unconstrained reaches fuel) edge.children index rest current)
              (by
                intro fuel extra edge current answer final done
                cases selected : edge.children[index]? with
                | none => simpa [child, selected] using done
                | some value =>
                    simpa only [child, selected] using
                      fuel_stable unconstrained reaches fuel extra rest value current answer final (by simpa only [child, selected] using done)) tests
            exact ⟨fuel + 1, answer, final, by
                simpa only [nodeMeets, dispatch, original, Value.depth, Value.free, finite, Bool.false_eq_true, ↓reduceIte] using done,
              growth, history⟩
termination_by (path.length, rank node.value)
decreasing_by
  · apply Prod.Lex.left
    simp
  · exact Prod.Lex.right _ smaller

/-- Every source edge-path query completes in its actual input cache. -/
theorem meets_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (path : Path) :
    Completes node.state (fun fuel => meets unconstrained reaches fuel values path node.state) := by
  cases path with
  | nil => exact immediate node _ 0 false rfl
  | cons index rest =>
      cases selected : values[index]? with
      | none => exact immediate node _ 0 false (by simp [meets, child, selected])
      | some value =>
          let next : Node Symbol Guard := { node with value := value, available := available value (List.mem_of_getElem? selected) }
          simpa only [meets, child, selected] using node_complete unconstrained reaches rest next

/-- A complete equality class has finite ordered evaluation with actual shared cache effects. -/
theorem class_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    Completes node.state (fun fuel => classMeets unconstrained reaches fuel values paths node.state) := by
  apply anyKnown_complete node paths (fun fuel path current => meets unconstrained reaches fuel values path current)
    (fun fuel extra path current answer final done => meets_fuel_stable unconstrained reaches fuel extra values path current answer final done)
  intro path member current growth history
  exact meets_complete unconstrained reaches current values
    (fun value member => (available value member).grows node.state current.state growth history) path

/-- Every finite path eventually returns a fixed Boolean and exact final certified cache. -/
theorem node_eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (path : Path) (node : Node Symbol Guard) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, nodeMeets unconstrained reaches (bound + extra) path node.value node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, done, growth, history⟩ := node_complete unconstrained reaches path node
  exact ⟨fuel, answer, after, growth, history, fun extra => fuel_stable unconstrained reaches fuel extra path node.value node.state answer after.state done⟩

/-- Every edge path eventually returns a fixed Boolean and exact final certified cache. -/
theorem meets_eventually_exact [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (path : Path) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, meets unconstrained reaches (bound + extra) values path node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, done, growth, history⟩ := meets_complete unconstrained reaches node values available path
  exact ⟨fuel, answer, after, growth, history,
    fun extra => meets_fuel_stable unconstrained reaches fuel extra values path node.state answer after.state done⟩

/-- Every equality class eventually returns a fixed Boolean and exact final certified shared cache. -/
theorem class_eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, classMeets unconstrained reaches (bound + extra) values paths node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, done, growth, history⟩ := class_complete unconstrained reaches node values available paths
  exact ⟨fuel, answer, after, growth, history, fun extra => class_fuel_stable unconstrained reaches fuel extra values paths node.state answer after.state done⟩

/-- Original source construction derives finite current-policy node traces and both histories. -/
theorem source_node_trace [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained reaches : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard,
        NodeTrace unconstrained reaches path value state answer after.state ∧
        Grows state after.state ∧ Extends state.nodes.issued after.state.nodes.issued ∧
        ∀ extra, nodeMeets unconstrained reaches (bound + extra) path value state = .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro path
  obtain ⟨fuel, answer, after, growth, history, stable⟩ :=
    node_eventually_exact unconstrained reaches path (fromCompleted expression value state done)
  have actual := stable 0
  rw [Nat.add_zero] at actual
  exact ⟨fuel, answer, after, node_trace_of_done unconstrained reaches fuel path value state answer after.state actual,
    growth, history, stable⟩

/-- Every original source edge has finite exact class checks without supplied cache premises. -/
theorem source_edge_classes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained reaches : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ paths,
        ∃ bound answer, ∃ after : Node Symbol Guard,
          Grows state after.state ∧ Extends state.nodes.issued after.state.nodes.issued ∧
          ∀ extra, classMeets unconstrained reaches (bound + extra) edge.children paths state = .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member paths
  let node := fromCompleted expression value state done
  apply class_eventually_exact unconstrained reaches node edge.children ?_ paths
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

end MicroCFTA.EndpointStatefulGateCompletion
