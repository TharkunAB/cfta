import MicroCFTA.InternedFreshOrdinaryStatefulGate
import MicroCFTA.InternedFreshOrdinaryGateRank

/-!
# Finite ordered gate evaluation in returned source caches

Each completed query retains its actual cache and both growth histories.
The next sibling therefore retains every original available input. Finite
child lists and the strict open-Mu rank give finite gate evaluation.
-/
namespace MicroCFTA.InternedFreshOrdinaryStatefulGateCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryGateRank (Node step)
open InternedFreshOrdinaryStatefulGate
open InternedFreeOccurrenceRank (rank)
open EqualityNormalize

/-- A finite Boolean evaluation returns its actual complete cache and both histories. -/
def Completes (before : State Symbol Guard) (work : Nat → Outcome Symbol Guard (Option Bool)) : Prop :=
  ∃ fuel answer, ∃ after : Node Symbol Guard, work fuel = .done (some answer) after.state ∧
    Grows before after.state ∧ Extends before.nodes.issued after.state.nodes.issued

/-- An immediate Boolean result retains its exact initial cache. -/
theorem immediate (node : Node Symbol Guard) (work : Nat → Outcome Symbol Guard (Option Bool))
    (fuel : Nat) (answer : Bool) (done : work fuel = .done (some answer) node.state) : Completes node.state work :=
  ⟨fuel, answer, node, done, grows_refl _, extends_refl _⟩

/-- The actual certified unfolding step retains both cache histories. -/
theorem step_growth [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard) :
    Grows node.state (step node).result.state ∧
      Extends node.state.nodes.issued (step node).result.state.nodes.issued := by
  obtain ⟨value, after, done, _, _, _, _, _, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_costs node.value node.state
      node.context node.depth node.costs node.covered node.available
  rw [(step node).actual] at done
  cases done
  exact ⟨growth, history⟩

/-- Ordered disjunction completes when every requested test completes in each retained cache. -/
theorem anyKnown_complete (node : Node Symbol Guard) (items : List Item)
    (test : Nat → Item → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (stable : ∀ fuel extra item state answer final, test fuel item state = .done (some answer) final →
      test (fuel + extra) item state = .done (some answer) final)
    (complete : ∀ item ∈ items, ∀ current : Node Symbol Guard,
      Grows node.state current.state → Extends node.state.nodes.issued current.state.nodes.issued →
      Completes current.state (fun fuel => test fuel item current.state)) :
    Completes node.state (fun fuel => anyKnown (test fuel) items node.state) := by
  induction items generalizing node with
  | nil => exact immediate node _ 0 false rfl
  | cons first rest ih =>
      obtain ⟨headFuel, answer, middle, headDone, headGrowth, headHistory⟩ :=
        complete first List.mem_cons_self node (grows_refl _) (extends_refl _)
      cases answer with
      | true =>
          exact ⟨headFuel, true, middle, by simp only [anyKnown, headDone, Outcome.bind], headGrowth, headHistory⟩
      | false =>
          obtain ⟨tailFuel, result, final, tailDone, tailGrowth, tailHistory⟩ := ih middle
            (fun item member current growth history => complete item (List.mem_cons_of_mem first member) current
              (grows_trans headGrowth growth) (extends_trans headHistory history))
          have headMore := stable headFuel tailFuel first node.state false middle.state headDone
          have tailMore : anyKnown (test (headFuel + tailFuel)) rest middle.state = .done (some result) final.state := by
            simpa only [Nat.add_comm] using anyKnown_stable (test tailFuel) (test (tailFuel + headFuel))
              (fun item state answer final done => stable tailFuel headFuel item state answer final done)
              rest middle.state result final.state tailDone
          exact ⟨headFuel + tailFuel, result, final, by simp only [anyKnown, headMore, Outcome.bind, tailMore],
            grows_trans headGrowth tailGrowth, extends_trans headHistory tailHistory⟩

/-- Every actual stateful gate query completes, including ordered sibling effects and open nested Mu. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (node : Node Symbol Guard) :
    Completes node.state (fun fuel => nodeMeets unconstrained fuel path node.value node.state) := by
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
          obtain ⟨fuel, answer, final, done, growth, history⟩ := node_complete unconstrained path (step node).result
          have first := step_growth node
          exact ⟨fuel + 1, answer, final, by
              simpa [nodeMeets, dispatch, original, Value.depth, constrained, closed, actual, Outcome.bind] using done,
            grows_trans first.1 growth, extends_trans first.2 history⟩
  | node entry edges depth free =>
      by_cases finite : (depth == 0 && free.isEmpty) = true
      · exact immediate node _ 1 false (by simp only [nodeMeets, dispatch, Value.depth, Value.free, finite, ↓reduceIte])
      · cases path with
        | nil => exact immediate node _ 1 (!free.isEmpty) (by simp only [nodeMeets, dispatch, Value.depth, Value.free, finite, Bool.false_eq_true, ↓reduceIte])
        | cons index rest =>
            have tests : ∀ edge ∈ edges, ∀ current : Node Symbol Guard,
                Grows node.state current.state → Extends node.state.nodes.issued current.state.nodes.issued →
                Completes current.state (fun fuel => child (nodeMeets unconstrained fuel) edge.children index rest current.state) := by
              intro edge member current growth history
              cases selected : edge.children[index]? with
              | none => exact immediate current _ 0 false (by simp [child, selected])
              | some value =>
                  have available : Available node.state value := by
                    apply node.available.children value
                    rw [original]
                    exact List.mem_flatMap.mpr ⟨edge, member, List.mem_of_getElem? selected⟩
                  let next : Node Symbol Guard := { current with value := value, available := available.grows node.state current.state growth history }
                  simpa only [child, selected] using node_complete unconstrained rest next
            obtain ⟨fuel, answer, final, done, growth, history⟩ := anyKnown_complete node edges
              (fun fuel edge current => child (nodeMeets unconstrained fuel) edge.children index rest current)
              (by
                intro fuel extra edge current answer final done
                cases selected : edge.children[index]? with
                | none => simpa [child, selected] using done
                | some value =>
                    simpa only [child, selected] using
                      fuel_stable unconstrained fuel extra rest value current answer final (by simpa only [child, selected] using done)) tests
            exact ⟨fuel + 1, answer, final, by
                simpa only [nodeMeets, dispatch, original, Value.depth, Value.free, finite, Bool.false_eq_true, ↓reduceIte] using done,
              growth, history⟩
termination_by (path.length, rank node.value)
decreasing_by
  · apply Prod.Lex.left
    simp
  · exact Prod.Lex.right _ smaller

/-- Every source edge-path query completes in its actual input cache. -/
theorem meets_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (path : Path) :
    Completes node.state (fun fuel => meets unconstrained fuel values path node.state) := by
  cases path with
  | nil => exact immediate node _ 0 false rfl
  | cons index rest =>
      cases selected : values[index]? with
      | none => exact immediate node _ 0 false (by simp [meets, child, selected])
      | some value =>
          let next : Node Symbol Guard := { node with value := value, available := available value (List.mem_of_getElem? selected) }
          simpa only [meets, child, selected] using node_complete unconstrained rest next

/-- A complete equality class has finite ordered evaluation with actual shared cache effects. -/
theorem class_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    Completes node.state (fun fuel => classMeets unconstrained fuel values paths node.state) := by
  apply anyKnown_complete node paths (fun fuel path current => meets unconstrained fuel values path current)
    (fun fuel extra path current answer final done => meets_fuel_stable unconstrained fuel extra values path current answer final done)
  intro path member current growth history
  exact meets_complete unconstrained current values
    (fun value member => (available value member).grows node.state current.state growth history) path

/-- Every finite path eventually returns a fixed Boolean and exact final certified cache. -/
theorem node_eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (node : Node Symbol Guard) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, nodeMeets unconstrained (bound + extra) path node.value node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, done, growth, history⟩ := node_complete unconstrained path node
  exact ⟨fuel, answer, after, growth, history, fun extra => fuel_stable unconstrained fuel extra path node.value node.state answer after.state done⟩

/-- Every equality class eventually returns a fixed Boolean and exact final certified shared cache. -/
theorem class_eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, classMeets unconstrained (bound + extra) values paths node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, done, growth, history⟩ := class_complete unconstrained node values available paths
  exact ⟨fuel, answer, after, growth, history, fun extra => class_fuel_stable unconstrained fuel extra values paths node.state answer after.state done⟩

end MicroCFTA.InternedFreshOrdinaryStatefulGateCompletion
