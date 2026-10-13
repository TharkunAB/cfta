import MicroCFTA.SourceSymbolicIndex
import MicroCFTA.SolverAdapter

/-!
# Bounded import dispatch and residual checks

The ordered constraint scan retains the first unsupported guard. Only that
error selects bounded denotation. Pruning errors remain errors. The negative
bound returns the empty grouped generator before any external call.
-/
namespace MicroCFTA.SourceCompileImport
open SourceGuards SourceSymbolicIndex

/-- Check each reachable edge constraint in source row order. -/
def scan : List (Constraint Formula) → Except (Guard Formula) Unit
  | [] => .ok ()
  | first :: rest => do
      let _ ← SourceIndicatorCompiler.constraintIndicators first.equalities first.guard
      scan rest

/-- The source scan succeeds exactly when every constraint compiles. -/
theorem scan_success (constraints : List (Constraint Formula)) :
    scan constraints = .ok () ↔ ∀ constraint ∈ constraints,
      ∃ rows, SourceIndicatorCompiler.constraintIndicators constraint.equalities constraint.guard = .ok rows := by
  induction constraints with
  | nil => simp [scan]
  | cons first rest ih =>
      cases compiled : SourceIndicatorCompiler.constraintIndicators first.equalities first.guard with
      | error bad => simp [scan, compiled, Bind.bind, Except.bind]
      | ok rows => simp [scan, compiled, Bind.bind, Except.bind, ih]

/-- A compiled prefix cannot hide or replace the first unsupported guard. -/
theorem scan_first_error (initial : List (Constraint Formula))
    (prefixOk : scan initial = .ok ()) (constraint : Constraint Formula) (bad : Guard Formula)
    (failed : SourceIndicatorCompiler.constraintIndicators constraint.equalities constraint.guard = .error bad)
    (rest : List (Constraint Formula)) : scan (initial ++ constraint :: rest) = .error bad := by
  induction initial with
  | nil => simp [scan, failed, Bind.bind, Except.bind]
  | cons first tail ih =>
      cases compiled : SourceIndicatorCompiler.constraintIndicators first.equalities first.guard with
      | error bad => simp [scan, compiled, Bind.bind, Except.bind] at prefixOk
      | ok rows =>
          simp only [scan, compiled, Bind.bind, Except.bind] at prefixOk
          simpa [scan, compiled, Bind.bind, Except.bind] using ih prefixOk

/-- Every scan error identifies its successful prefix and exact failing constraint. -/
theorem scan_error_origin (constraints : List (Constraint Formula)) (bad : Guard Formula)
    (failed : scan constraints = .error bad) :
    ∃ initial constraint rest, constraints = initial ++ constraint :: rest ∧
      scan initial = .ok () ∧
      SourceIndicatorCompiler.constraintIndicators constraint.equalities constraint.guard = .error bad := by
  induction constraints with
  | nil => cases failed
  | cons first tail ih =>
      cases compiled : SourceIndicatorCompiler.constraintIndicators first.equalities first.guard with
      | error error =>
          have same : error = bad := by simpa [scan, compiled, Bind.bind, Except.bind] using failed
          exact ⟨[], first, tail, rfl, rfl, same ▸ compiled⟩
      | ok rows =>
          have tailFailed : scan tail = .error bad := by
            simpa [scan, compiled, Bind.bind, Except.bind] using failed
          obtain ⟨initial, constraint, rest, shape, prefixOk, origin⟩ := ih tailFailed
          refine ⟨first :: initial, constraint, rest, ?_, ?_, origin⟩
          · simp [shape]
          · simp [scan, compiled, prefixOk, Bind.bind, Except.bind]

/-- Pruning distinguishes an undecided edge from invalid reconstruction. -/
inductive PruneError (Unknown Invalid : Type) where
  | unknown (edge : Unknown)
  | invalid (reason : Invalid)

/-- These are the public errors that this import path can return. -/
inductive Error (Formula Invalid : Type) where
  | solverUnknown
  | invalidPruning (reason : Invalid)
  | residualGuard (guard : Guard Formula)
  | solverTimeLimit (milliseconds : Int)

/-- The scan either returns a reduced graph, an error, or a bounded fallback request. -/
inductive Route (Formula Invalid Graph : Type) where
  | returned (result : Except (Error Formula Invalid) Graph)
  | denoted (depth : Int) (guard : Guard Formula)

/-- Match the nested source case after the pruning call has completed. -/
def route (constraints : Graph → List (Constraint Formula)) (bound : Option Int)
    (pruned : Except (PruneError Unknown Invalid) Graph) : Route Formula Invalid Graph :=
  match pruned with
  | .error (.unknown _) => .returned (.error .solverUnknown)
  | .error (.invalid reason) => .returned (.error (.invalidPruning reason))
  | .ok reduced =>
      match scan (constraints reduced) with
      | .ok () => .returned (.ok reduced)
      | .error guard =>
          match bound with
          | none => .returned (.error (.residualGuard guard))
          | some depth => .denoted depth guard

/-- A fallback request requires successful pruning and the exact scan failure. -/
theorem route_denoted_iff (constraints : Graph → List (Constraint Formula)) (bound : Option Int)
    (pruned : Except (PruneError Unknown Invalid) Graph) (depth : Int) (guard : Guard Formula) :
    route constraints bound pruned = .denoted depth guard ↔
      ∃ reduced, pruned = .ok reduced ∧ bound = some depth ∧ scan (constraints reduced) = .error guard := by
  cases pruned with
  | error error => cases error <;> simp [route]
  | ok reduced =>
      cases checked : scan (constraints reduced) with
      | ok value => cases value; simp [route, checked]
      | error bad => cases bound <;> simp [route, checked, and_comm]

/-- A successful indicator scan retains the reduced graph, including its row order. -/
theorem route_success (constraints : Graph → List (Constraint Formula)) (bound : Option Int)
    (pruned : Except (PruneError Unknown Invalid) Graph) (reduced : Graph) :
    route constraints bound pruned = .returned (.ok reduced) ↔
      pruned = .ok reduced ∧ scan (constraints reduced) = .ok () := by
  cases pruned with
  | error error => cases error <;> simp [route]
  | ok graph =>
      cases checked : scan (constraints graph) with
      | ok value => cases value; simp [route, checked, eq_comm]; intro same; subst graph; exact checked
      | error bad =>
          cases bound <;> simp [route, checked] <;> intro same <;> subst graph <;> simp [checked]

/-- Finish the denotation callback, preserving the original residual guard on build failure. -/
def finish (rebuild : List Term → Except BuildError Graph) (grouped : Graph → Value)
    (guard : Guard Formula) (accepted : Except Unknown (List Term)) : Except (Error Formula Invalid) Value :=
  match accepted with
  | .error _ => .error .solverUnknown
  | .ok terms =>
      match rebuild terms with
      | .error _ => .error (.residualGuard guard)
      | .ok graph => .ok (grouped graph)

/-- A successful fallback output comes from its accepted terms and successful reconstruction. -/
theorem finish_success (rebuild : List Term → Except BuildError Graph) (grouped : Graph → Value)
    (guard : Guard Formula) (accepted : Except Unknown (List Term)) (output : Value) :
    finish (Invalid := Invalid) rebuild grouped guard accepted = .ok output ↔
      ∃ terms graph, accepted = .ok terms ∧ rebuild terms = .ok graph ∧ grouped graph = output := by
  cases accepted with
  | error error => simp [finish]
  | ok terms =>
      cases built : rebuild terms <;> simp [finish, built]

/-- The public wrapper catches only time-limit exceptions. -/
def reportTimeLimit : Except SolverAdapter.Failure (Except (Error Formula Invalid) Value) →
    Except SolverAdapter.Failure (Except (Error Formula Invalid) Value)
  | .error (.timeLimit milliseconds) => .ok (.error (.solverTimeLimit milliseconds))
  | result => result

/-- A time limit becomes the public timeout error, not SolverUnknown. -/
theorem timeLimit_reported (milliseconds : Int) :
    reportTimeLimit (Formula := Formula) (Invalid := Invalid) (Value := Value)
      (.error (.timeLimit milliseconds)) = .ok (.error (.solverTimeLimit milliseconds)) := rfl

/-- Other IO failures still propagate through the public wrapper. -/
theorem other_failure_preserved (failure : SolverAdapter.Failure)
    (notLimit : ∀ milliseconds, failure ≠ .timeLimit milliseconds) :
    reportTimeLimit (Formula := Formula) (Invalid := Invalid) (Value := Value) (.error failure) =
      .error failure := by
  cases failure <;> simp_all [reportTimeLimit]

end MicroCFTA.SourceCompileImport
