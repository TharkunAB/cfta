import MicroCFTA.InternedFreshOrdinaryStatefulGateGraph

/-!
# Complete class traces from actual source construction

Logical path and class graphs retain ordered short circuit and shared
returned caches. Their finite executions have exact Boolean and cache
readback. Original source construction derives the initial cache premises.
-/
namespace MicroCFTA.InternedFreshOrdinaryStatefulGateTrace
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedRecordCoherence InternedProbeProvenance InternedFreshOrdinaryContext
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedFreshOrdinaryStatefulGate InternedFreshOrdinaryStatefulGateCompletion
open EqualityNormalize

/-- An edge path starts below its root and follows its exact selected child. -/
inductive PathTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Path → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | empty : PathTrace unconstrained values [] state false state
  | child (trace : ChildTrace unconstrained values index rest state answer final) :
      PathTrace unconstrained values (index :: rest) state answer final

/-- A class follows original path order and stops at the first true decision. -/
inductive ClassTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Class → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | nil : ClassTrace unconstrained values [] state false state
  | stop (head : PathTrace unconstrained values path state true final) :
      ClassTrace unconstrained values (path :: rest) state true final
  | next (head : PathTrace unconstrained values path state false middle)
      (tail : ClassTrace unconstrained values rest middle answer final) :
      ClassTrace unconstrained values (path :: rest) state answer final

/-- Every completed path worker follows its logical source graph. -/
theorem path_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : meets unconstrained fuel values path state = .done (some answer) final) :
    PathTrace unconstrained values path state answer final := by
  cases path with
  | nil =>
      simp only [meets, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .empty
  | cons index rest =>
      exact .child (child_trace_of_done unconstrained fuel (node_trace_of_done unconstrained fuel) values index rest state answer final done)

/-- Every logical path graph has a finite execution with the exact final cache. -/
theorem path_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : PathTrace unconstrained values path state answer final) :
    ∃ fuel, meets unconstrained fuel values path state = .done (some answer) final := by
  cases trace with
  | empty => exact ⟨0, rfl⟩
  | child trace => exact child_trace_complete _ _ _ _ _ _ _ trace

/-- A completed class worker retains the exact logical ordered path trace. -/
theorem class_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained fuel values paths state = .done (some answer) final) :
    ClassTrace unconstrained values paths state answer final := by
  induction paths generalizing state with
  | nil =>
      simp only [classMeets, anyKnown, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases found : meets unconstrained fuel values first state with
      | pending key after => simp [classMeets, anyKnown, found, Outcome.bind] at done
      | done result after =>
          cases result with
          | none => simp [classMeets, anyKnown, found, Outcome.bind] at done
          | some result =>
              have head := path_trace_of_done unconstrained fuel values first state result after found
              cases result with
              | false => exact .next head (ih after (by simpa only [classMeets, anyKnown, found, Outcome.bind] using done))
              | true =>
                  simp only [classMeets, anyKnown, found, Outcome.bind, Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .stop head

/-- Every logical class graph has finite execution with the same ordered cache effects. -/
theorem class_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ClassTrace unconstrained values paths state answer final) :
    ∃ fuel, classMeets unconstrained fuel values paths state = .done (some answer) final := by
  induction trace with
  | nil => exact ⟨0, rfl⟩
  | stop head =>
      obtain ⟨fuel, done⟩ := path_trace_complete _ _ _ _ _ _ head
      exact ⟨fuel, by simp only [classMeets, anyKnown, done, Outcome.bind]⟩
  | next head tail ih =>
      obtain ⟨headFuel, headDone⟩ := path_trace_complete _ _ _ _ _ _ head
      obtain ⟨tailFuel, tailDone⟩ := ih
      have headMore := meets_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ headDone
      have tailMore := class_fuel_stable unconstrained tailFuel headFuel _ _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      simpa only [classMeets, anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore

/-- The logical class graph is exactly finite actual stateful class execution. -/
theorem class_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) :
    ClassTrace unconstrained values paths state answer final ↔
      ∃ fuel, classMeets unconstrained fuel values paths state = .done (some answer) final := by
  constructor
  · exact class_trace_complete unconstrained values paths state answer final
  · rintro ⟨fuel, done⟩
    exact class_trace_of_done unconstrained fuel values paths state answer final done

/-- Class traces are functional in the Boolean decision and the complete final shared cache. -/
theorem class_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : ClassTrace unconstrained values paths state first firstState)
    (right : ClassTrace unconstrained values paths state second secondState) : first = second ∧ firstState = secondState := by
  obtain ⟨leftFuel, leftDone⟩ := class_trace_complete unconstrained values paths state first firstState left
  obtain ⟨rightFuel, rightDone⟩ := class_trace_complete unconstrained values paths state second secondState right
  have leftMore := class_fuel_stable unconstrained leftFuel rightFuel values paths state first firstState leftDone
  have rightMore := class_fuel_stable unconstrained rightFuel leftFuel values paths state second secondState rightDone
  have equal := leftMore.symm.trans (by simpa only [Nat.add_comm] using rightMore)
  simpa only [Outcome.done.injEq, Option.some.injEq] using equal

/-- Every certified class has a logical trace and an exact stable finite execution with all returned cache invariants. -/
theorem cached_class_trace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    ∃ bound answer, ∃ after : Node Symbol Guard,
      ClassTrace unconstrained values paths node.state answer after.state ∧
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, classMeets unconstrained (bound + extra) values paths node.state = .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, growth, history, stable⟩ := class_eventually_exact unconstrained node values available paths
  have done := stable 0
  rw [Nat.add_zero] at done
  exact ⟨fuel, answer, after, class_trace_of_done unconstrained fuel values paths node.state answer after.state done,
    growth, history, stable⟩

/-- Original source construction derives finite stateful gate traces at every finite path. -/
theorem source_node_trace [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard,
        NodeTrace unconstrained path value state answer after.state ∧
        Grows state after.state ∧ Extends state.nodes.issued after.state.nodes.issued ∧
        ∀ extra, nodeMeets unconstrained (bound + extra) path value state = .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro path
  obtain ⟨fuel, answer, after, growth, history, stable⟩ :=
    node_eventually_exact unconstrained path (fromCompleted expression value state done)
  have actual := stable 0
  rw [Nat.add_zero] at actual
  exact ⟨fuel, answer, after, node_trace_of_done unconstrained fuel path value state answer after.state actual,
    growth, history, stable⟩

/-- Every original outgoing source edge has finite exact class traces without supplied cache premises. -/
theorem source_edge_classes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ paths,
        ∃ bound answer, ∃ after : Node Symbol Guard,
          ClassTrace unconstrained edge.children paths state answer after.state ∧
          Grows state after.state ∧ Extends state.nodes.issued after.state.nodes.issued ∧
          ∀ extra, classMeets unconstrained (bound + extra) edge.children paths state = .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member paths
  let node := fromCompleted expression value state done
  apply cached_class_trace unconstrained node edge.children ?_ paths
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

end MicroCFTA.InternedFreshOrdinaryStatefulGateTrace
