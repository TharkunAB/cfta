import MicroCFTA.SourceDenotationRuns

/-!
# Exact andM and filterM equations

This deterministic reading is only a source-correspondence lemma. The public
execution and adequacy theorems use occurrence-specific traces and do not
require this fixed reply function.
-/

namespace MicroCFTA.SourceDenotationFilterM

open SourceDenotationEffects SourceSizedLiquidExecution SolverAdapter

/-- The source decide branch preserves its exact unknown item or external exception. -/
def decide (answer : Item → Result) (item : Item) : Except (Halt Item) Bool :=
  match answer item with
  | .raised failure => .error (.raised failure)
  | .returned .unknown => .error (.unknown item)
  | .returned .no => .ok false
  | .returned .yes => .ok true

/-- The source andM evaluates the remaining list only after a True result. -/
def all (answer : Item → Result) : List Item → Except (Halt Item) Bool
  | [] => .ok true
  | item :: rest => do
      let accepted ← decide answer item
      if accepted then all answer rest else pure false

/-- The exact source filterM traverses ordered run rows before deduplication. -/
def filter (answer : Item → Result) : List (Value × List Item) →
    Except (Halt Item) (List (Value × List Item))
  | [] => .ok []
  | row :: rest => do
      let accepted ← all answer row.2
      if accepted then (filter answer rest).map (row :: ·) else filter answer rest

/-- Every fixed-reply residual trace has exactly the source andM result. -/
theorem all_trace (answer : Item → Result) {items result work}
    (run : AllRun (fun item _ result => result = answer item) items result work) :
    result = all answer items := by
  induction run with
  | nil => rfl
  | unknown called => simp [all, decide, ← called, bind, Except.bind]
  | raised called => simp [all, decide, ← called, bind, Except.bind]
  | no called => simp [all, decide, ← called, bind, Except.bind, pure, Except.pure]
  | yes called tail ih => simpa [all, decide, ← called, bind, Except.bind, pure, Except.pure] using ih

/-- Every fixed-reply run filter is the actual source filterM computation. -/
theorem filter_trace (answer : Item → Result) {rows : List (Value × List Item)} {result work}
    (run : SourceDenotationEffects.FilterRun (fun item _ result => result = answer item) rows result work) :
    result = filter answer rows := by
  induction run with
  | nil => rfl
  | error failed => simp [filter, bind, Except.bind, ← all_trace answer failed]
  | no rejected tail ih => simpa [filter, bind, Except.bind, Except.map, ← all_trace answer rejected] using ih
  | yesOk accepted tail ih => simp [filter, bind, Except.bind, Except.map, ← all_trace answer accepted, ← ih]
  | yesError accepted tail ih => simp [filter, bind, Except.bind, Except.map, ← all_trace answer accepted, ← ih]

/-- The complete constrained branch is filterM followed by ordered first-occurrence nubOrd. -/
theorem denotation_trace [DecidableEq Value] (answer : Item → Result)
    (rows : List (Value × List Item)) {result work}
    (run : SourceDenotationRuns.Run (fun item _ result => result = answer item) rows result work) :
    result = (filter answer rows).map SourceDenotationRuns.finish := by
  cases run with
  | done filtered => rw [← filter_trace answer filtered]

end MicroCFTA.SourceDenotationFilterM
