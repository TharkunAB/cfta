import MicroCFTA.EndpointStatefulGate

/-!
# Logical execution graph of the current endpoint gate

The graph has no gate fuel. It records the actual unfolding equations and
the cache at each visited query. True results omit later queries. False
results pass their exact returned cache to the next sibling. The endpoint
read is explicit. Global predicate memos require a separate source bridge.
-/
namespace MicroCFTA.EndpointStatefulGateTrace
open InternedConstructorTemplates InternedNestedConstruction
open EndpointStatefulGate
open InternedFreshOrdinaryStatefulGate (anyKnown child anyKnown_stable)
open EqualityNormalize

mutual
/-- The source gate's logical graph retains its decision and complete cache trace. -/
inductive NodeTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool) :
    Path → Value Symbol Guard → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | empty : NodeTrace unconstrained reaches path .empty state false state
  | reference : NodeTrace unconstrained reaches path (.reference name) state true state
  | union (members : List (Value Symbol Guard)) : NodeTrace unconstrained reaches path (.union entry members depth free) state true state
  | finite (fast : (depth == 0 && free.isEmpty) = true) :
      NodeTrace unconstrained reaches path (.node entry edges depth free) state false state
  | endpoint (slow : (depth == 0 && free.isEmpty) = false) :
      NodeTrace unconstrained reaches [] (.node entry edges depth free) state (!free.isEmpty || reaches (.node entry edges depth free)) state
  | branches (slow : (depth == 0 && free.isEmpty) = false)
      (trace : EdgesTrace unconstrained reaches index rest edges state answer final) :
      NodeTrace unconstrained reaches (index :: rest) (.node entry edges depth free) state answer final
  | constrained (blocked : unconstrained (.mu entry body depth ordinary) = false) :
      NodeTrace unconstrained reaches path (.mu entry body depth ordinary) state true state
  | closed (plain : unconstrained (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true) :
      NodeTrace unconstrained reaches path (.mu entry body depth ordinary) state false state
  | unfold (plain : unconstrained (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (trace : NodeTrace unconstrained reaches path next after answer final) :
      NodeTrace unconstrained reaches path (.mu entry body depth ordinary) state answer final

/-- A child lookup either returns false immediately or follows the exact selected source child. -/
inductive ChildTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool) :
    List (Value Symbol Guard) → Nat → Path → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | missing (absent : values[index]? = none) : ChildTrace unconstrained reaches values index path state false state
  | present (found : values[index]? = some value) (trace : NodeTrace unconstrained reaches path value state answer final) :
      ChildTrace unconstrained reaches values index path state answer final

/-- Ordered edge disjunction threads false results and stops at its first true result. -/
inductive EdgesTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool) :
    Nat → Path → List (EdgeValue Symbol Guard) → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | nil : EdgesTrace unconstrained reaches index path [] state false state
  | stop (head : ChildTrace unconstrained reaches edge.children index path state true final) :
      EdgesTrace unconstrained reaches index path (edge :: rest) state true final
  | next (head : ChildTrace unconstrained reaches edge.children index path state false middle)
      (tail : EdgesTrace unconstrained reaches index path rest middle answer final) :
      EdgesTrace unconstrained reaches index path (edge :: rest) state answer final
end

/-- A completed child worker follows the corresponding logical lookup and source query. -/
theorem child_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (sound : ∀ path value state answer final,
      nodeMeets unconstrained reaches fuel path value state = .done (some answer) final →
      NodeTrace unconstrained reaches path value state answer final)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : child (nodeMeets unconstrained reaches fuel) values index path state = .done (some answer) final) :
    ChildTrace unconstrained reaches values index path state answer final := by
  cases found : values[index]? with
  | none =>
      simp only [child, found, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .missing found
  | some value => exact .present found (sound path value state answer final (by simpa only [child, found] using done))

/-- A completed edge scan has the same ordered logical trace and exact intermediate caches. -/
theorem edges_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (sound : ∀ path value state answer final,
      nodeMeets unconstrained reaches fuel path value state = .done (some answer) final →
      NodeTrace unconstrained reaches path value state answer final)
    (edges : List (EdgeValue Symbol Guard)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : anyKnown (fun edge current => child (nodeMeets unconstrained reaches fuel) edge.children index path current)
      edges state = .done (some answer) final) : EdgesTrace unconstrained reaches index path edges state answer final := by
  induction edges generalizing state with
  | nil =>
      simp only [anyKnown, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases found : child (nodeMeets unconstrained reaches fuel) first.children index path state with
      | pending key after => simp [anyKnown, found, Outcome.bind] at done
      | done result after =>
          cases result with
          | none => simp [anyKnown, found, Outcome.bind] at done
          | some result =>
              have head := child_trace_of_done unconstrained reaches fuel sound first.children index path state result after found
              cases result with
              | false => exact .next head (ih after (by simpa only [anyKnown, found, Outcome.bind] using done))
              | true =>
                  simp only [anyKnown, found, Outcome.bind, Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .stop head

/-- Every completed instrumented gate query has an unbounded source execution graph. -/
theorem node_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : nodeMeets unconstrained reaches fuel path value state = .done (some answer) final) :
    NodeTrace unconstrained reaches path value state answer final := by
  induction fuel generalizing path value state answer final with
  | zero => simp [nodeMeets] at done
  | succ fuel ih =>
      cases value with
      | empty =>
          simp [nodeMeets, dispatch, Value.depth, Value.free] at done
          rcases done with ⟨rfl, rfl⟩
          exact .empty
      | reference name =>
          simp only [nodeMeets, dispatch, Outcome.done.injEq, Option.some.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact .reference
      | union entry members depth free =>
          simp only [nodeMeets, dispatch, Outcome.done.injEq, Option.some.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact .union members
      | mu entry body depth ordinary =>
          cases plain : unconstrained (.mu entry body depth ordinary) with
          | false =>
              simp [nodeMeets, dispatch, Value.depth, plain] at done
              rcases done with ⟨rfl, rfl⟩
              exact .constrained plain
          | true =>
              cases closed : (Value.mu entry body depth ordinary).free.isEmpty with
              | true =>
                  simp [nodeMeets, dispatch, Value.depth, plain, closed] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .closed plain closed
              | false =>
                  simp [nodeMeets, dispatch, Value.depth, plain, closed] at done
                  cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                  | pending key after => simp [actual, Outcome.bind] at done
                  | done next after =>
                      exact .unfold plain closed actual (ih path next after answer final (by simpa only [actual, Outcome.bind] using done))
      | node entry edges depth free =>
          cases fast : depth == 0 && free.isEmpty with
          | true =>
              simp [nodeMeets, dispatch, Value.depth, Value.free, fast] at done
              rcases done with ⟨rfl, rfl⟩
              exact .finite fast
          | false =>
              cases path with
              | nil =>
                  simp only [nodeMeets, dispatch, Value.depth, Value.free, fast, Bool.false_eq_true, ↓reduceIte,
                    Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .endpoint fast
              | cons index rest =>
                  apply NodeTrace.branches fast
                  apply edges_trace_of_done unconstrained reaches fuel ih edges index rest state answer final
                  simpa only [nodeMeets, dispatch, Value.depth, Value.free, fast, Bool.false_eq_true, ↓reduceIte] using done

end MicroCFTA.EndpointStatefulGateTrace
