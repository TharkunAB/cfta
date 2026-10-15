import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.SourceEqualityPublicNativeEdge

/-!
# Actual indexed traversal of inherited source child constraints

The worker invokes each recursive node call at its actual child index and
returned warm state. Contradiction returns an equally sized empty forest.
Errors and incomplete callback observations retain their exact source scope.
The recursive node callback remains explicit until the outer caller is proved.
-/
namespace MicroCFTA.SourceEqualityInheritedChildren
open InternedConstructorTemplates SourceEqualityClassFoldGraph
universe u

/-- A child callback returns its complete answer and native state, or its actual incomplete observation. -/
inductive Result (width : Nat) (Symbol Guard Output : Type) (Observation : Type u) : Type u where
  | done (answer : Except String Output) (state : NativeState width Symbol Guard)
  | incomplete (observation : Observation)

/-- Continue only a successful callback and preserve every other observation without resuming. -/
def Result.bind (first : Result width Symbol Guard First Observation)
    (next : First → NativeState width Symbol Guard → Result width Symbol Guard Output Observation) : Result width Symbol Guard Output Observation :=
  match first with
  | .done (.ok value) state => next value state
  | .done (.error message) state => .done (.error message) state
  | .incomplete observation => .incomplete observation

/-- A successful continuation retains the exact completed first callback and its returned native state. -/
theorem Result.bind_done (first : Result width Symbol Guard First Observation)
    (next : First → NativeState width Symbol Guard → Result width Symbol Guard Output Observation)
    (result : Output) (after : NativeState width Symbol Guard) :
    first.bind next = .done (.ok result) after ↔
      ∃ value middle, first = .done (.ok value) middle ∧ next value middle = .done (.ok result) after := by
  cases first with
  | done answer state =>
      cases answer with
      | error => simp [Result.bind]
      | ok value =>
          constructor
          · intro done; exact ⟨value, state, rfl, done⟩
          · rintro ⟨actual, middle, same, done⟩; cases same; exact done
  | incomplete => simp [Result.bind]

/-- Source zipWith passes each child the constraints descended through its zero-based position. -/
def walk (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (payload : SourceEqualityPrecheck.Constraint) : Nat → List (Value Symbol Guard) → NativeState width Symbol Guard →
      Result width Symbol Guard (List (Value Symbol Guard)) Observation
  | _, [], state => .done (.ok []) state
  | index, value :: values, state =>
      (call (SourceEqualityDescend.descend payload index) value state).bind fun result middle =>
        (walk call payload (index + 1) values middle).bind fun results after => .done (.ok (result :: results)) after

/-- Actual contradiction skips all recursive calls; other payloads execute the literal indexed traversal. -/
def run (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (state : NativeState width Symbol Guard) :
    Result width Symbol Guard (List (Value Symbol Guard)) Observation :=
  match payload with
  | none => .done (.ok (values.map (fun _ => .empty))) state
  | some records => walk call (some records) 0 values state

/-- Every completed indexed graph keeps the exact recursive call receipt and next native state. -/
inductive Walk (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (payload : SourceEqualityPrecheck.Constraint) : Nat → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : Walk call payload index [] state [] state
  | cons (first : call (SourceEqualityDescend.descend payload index) value before = .done (.ok result) middle)
      (rest : Walk call payload (index + 1) values middle results after) :
      Walk call payload index (value :: values) before (result :: results) after

/-- The completed source graph retains both contradiction and live traversal cases. -/
inductive Graph (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation) :
    SourceEqualityPrecheck.Constraint → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | contradiction : Graph call none values state (values.map (fun _ => .empty)) state
  | live (actual : Walk call (some records) 0 values before results after) : Graph call (some records) values before results after

/-- Every complete indexed graph executes with the identical result and full native state. -/
theorem Walk.execute {call payload index values before results after} (trace : Walk (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload index values before results after) :
    walk call payload index values before = .done (.ok results) after := by
  induction trace with
  | nil => rfl
  | cons first _ ih => simp only [walk, first, Result.bind, ih]

/-- Every successful indexed worker result supplies its literal complete graph. -/
theorem walk_graph {call payload index values before results after}
    (done : walk (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload index values before = .done (.ok results) after) :
    Walk call payload index values before results after := by
  induction values generalizing index before results after with
  | nil => cases done; exact .nil
  | cons value values ih =>
      obtain ⟨result, middle, first, later⟩ := (Result.bind_done _ _ results after).mp done
      obtain ⟨rest, final, tail, returned⟩ := (Result.bind_done _ _ results after).mp later
      have parts := Result.done.inj returned
      have same := Except.ok.inj parts.1
      cases same; cases parts.2
      exact .cons first (ih tail)

/-- The source contradiction and indexed workers agree with their complete graphs in both directions. -/
theorem execution_iff {call payload values before results after} :
    Graph (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload values before results after ↔
      run call payload values before = .done (.ok results) after := by
  constructor
  · intro trace
    cases trace with
    | contradiction => rfl
    | live actual => exact actual.execute
  · intro done
    cases payload with
    | none => cases done; exact .contradiction
    | some records => exact .live (walk_graph done)

/-- Every successful indexed traversal preserves the source child arity. -/
theorem Walk.length {call payload index values before results after}
    (trace : Walk (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload index values before results after) : results.length = values.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

/-- Contradiction and live child traversal both take the equal-arity source setChildren branch. -/
theorem Graph.length {call payload values before results after}
    (trace : Graph (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload values before results after) : results.length = values.length := by
  cases trace with
  | contradiction => exact List.length_map _
  | live actual => exact actual.length

/-- An actual incomplete first callback is returned unchanged, without executing the tail. -/
theorem walk_incomplete {call payload index value values state observation}
    (actual : call (SourceEqualityDescend.descend payload index) value state = .incomplete observation) :
    walk (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload index (value :: values) state = .incomplete observation := by
  simp only [walk, actual, Result.bind]

/-- An actual first callback error keeps its exact full native state and does not execute the tail. -/
theorem walk_error {call payload index value values state message after}
    (actual : call (SourceEqualityDescend.descend payload index) value state = .done (.error message) after) :
    walk (Observation := Observation) (width := width) (Symbol := Symbol) (Guard := Guard) call payload index (value :: values) state = .done (.error message) after := by
  simp only [walk, actual, Result.bind]

end MicroCFTA.SourceEqualityInheritedChildren
