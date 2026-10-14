import MicroCFTA.InternedFreshOrdinaryStatefulGateTrace

/-!
# Adequacy and uniqueness of the ordered gate graph

Every logical source trace has finite executable fuel. Every completed
execution has that graph. Two logical traces therefore return the same
Boolean and the same final cache, including shared sibling effects.
-/
namespace MicroCFTA.InternedFreshOrdinaryStatefulGateTrace
open InternedConstructorTemplates InternedNestedConstruction
open InternedFreshOrdinaryStatefulGate
open EqualityNormalize

/-- A logical node trace has a finite execution with the exact result and final cache. -/
theorem node_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : NodeTrace unconstrained path value state answer final) :
    ∃ fuel, nodeMeets unconstrained fuel path value state = .done (some answer) final := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path state answer final _ =>
        ∃ fuel, child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final)
      (motive_3 := fun index path edges state answer final _ =>
        ∃ fuel, anyKnown (fun edge current => child (nodeMeets unconstrained fuel) edge.children index path current)
          edges state = .done (some answer) final) with
  | empty => exact ⟨1, by simp [nodeMeets, dispatch, Value.depth, Value.free]⟩
  | reference => exact ⟨1, by simp [nodeMeets, dispatch]⟩
  | union => exact ⟨1, by simp [nodeMeets, dispatch]⟩
  | finite fast => exact ⟨1, by simp only [nodeMeets, dispatch, Value.depth, Value.free, fast, ↓reduceIte]⟩
  | endpoint slow => exact ⟨1, by simp only [nodeMeets, dispatch, Value.depth, Value.free, slow, Bool.false_eq_true, ↓reduceIte]⟩
  | branches slow trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel + 1, by simpa only [nodeMeets, dispatch, Value.depth, Value.free, slow, Bool.false_eq_true, ↓reduceIte] using done⟩
  | constrained blocked => exact ⟨1, by simp [nodeMeets, dispatch, Value.depth, blocked]⟩
  | closed plain closed => exact ⟨1, by simp [nodeMeets, dispatch, Value.depth, plain, closed]⟩
  | unfold plain opened actual trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel + 1, by simpa [nodeMeets, dispatch, Value.depth, plain, opened, actual, Outcome.bind] using done⟩
  | missing absent => exact ⟨0, by simp [child, absent]⟩
  | present found trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel, by simpa only [child, found] using done⟩
  | nil => exact ⟨0, rfl⟩
  | stop head ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel, by simp only [anyKnown, done, Outcome.bind]⟩
  | next head tail headIH tailIH =>
      obtain ⟨headFuel, headDone⟩ := headIH
      obtain ⟨tailFuel, tailDone⟩ := tailIH
      have headMore := child_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ _ headDone
      have tailMore := anyKnown_stable _ _
        (fun edge current answer final done => child_fuel_stable unconstrained tailFuel headFuel
          edge.children _ _ current answer final done) _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      simpa only [anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore

/-- A logical child trace has finite execution at its exact selected source slot. -/
theorem child_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ChildTrace unconstrained values index path state answer final) :
    ∃ fuel, child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final := by
  cases trace with
  | missing absent => exact ⟨0, by simp [child, absent]⟩
  | present found trace =>
      obtain ⟨fuel, done⟩ := node_trace_complete _ _ _ _ _ _ trace
      exact ⟨fuel, by simpa only [child, found] using done⟩

/-- The source graph is equivalent to finite actual instrumented execution. -/
theorem node_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard) :
    NodeTrace unconstrained path value state answer final ↔
      ∃ fuel, nodeMeets unconstrained fuel path value state = .done (some answer) final := by
  constructor
  · exact node_trace_complete unconstrained path value state answer final
  · rintro ⟨fuel, done⟩
    exact node_trace_of_done unconstrained fuel path value state answer final done

/-- Logical source traces are functional in both Boolean output and complete final cache. -/
theorem node_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : NodeTrace unconstrained path value state first firstState)
    (right : NodeTrace unconstrained path value state second secondState) : first = second ∧ firstState = secondState := by
  obtain ⟨leftFuel, leftDone⟩ := node_trace_complete unconstrained path value state first firstState left
  obtain ⟨rightFuel, rightDone⟩ := node_trace_complete unconstrained path value state second secondState right
  have leftMore := fuel_stable unconstrained leftFuel rightFuel path value state first firstState leftDone
  have rightMore := fuel_stable unconstrained rightFuel leftFuel path value state second secondState rightDone
  have equal := leftMore.symm.trans (by simpa only [Nat.add_comm] using rightMore)
  simpa only [Outcome.done.injEq, Option.some.injEq] using equal

end MicroCFTA.InternedFreshOrdinaryStatefulGateTrace
