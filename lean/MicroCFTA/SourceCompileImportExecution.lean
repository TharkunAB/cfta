import MicroCFTA.SourceCompileImport

/-!
# Completed source import executions

This relation records each external call and its completed result. A fallback
queries the original graph at the requested depth. It does not query the
bounded graph passed to pruning or the graph returned by pruning. Completion
of external calls is an explicit premise, separate from finite local control.
-/
namespace MicroCFTA.SourceCompileImportExecution
open SourceCompileImport

/-- The finite operations surrounding the two external calls. -/
structure Operations (Formula Graph Term BuildError Value : Type) where
  constraints : Graph → List (SourceSymbolicIndex.Constraint Formula)
  boundDepth : Int → Graph → Graph
  rebuild : List Term → Except BuildError Graph
  grouped : Graph → Value
  empty : Value

/-- The argument passed to pruning applies the optional depth bound once. -/
def pruneInput (operations : Operations Formula Graph Term BuildError Value)
    (bound : Option Int) (source : Graph) : Graph :=
  match bound with
  | none => source
  | some depth => operations.boundDepth depth source

/-- Negative bounds return before either external operation. -/
def Live (bound : Option Int) : Prop := ∀ depth, bound = some depth → 0 ≤ depth

/-- Preserve call order and graph identity in the execution trace. -/
inductive Call (Graph : Type) where
  | prune (input : Graph)
  | denotation (depth : Int) (input : Graph)

/-- Source control after each requested IO action completes. -/
inductive Run (operations : Operations Formula Graph Term BuildError Value)
    (prunes : Graph → Nat → Except SolverAdapter.Failure (Except (PruneError Unknown Invalid) Graph) → Prop)
    (denotes : Int → Graph → Nat → Except SolverAdapter.Failure (Except DenotationUnknown (List Term)) → Prop)
    (source : Graph) : Option Int → Except SolverAdapter.Failure (Except (Error Formula Invalid) Value) →
      List (Call Graph) → Nat → Prop where
  | negative : depth < 0 → Run operations prunes denotes source (some depth) (.ok (.ok operations.empty)) [] 1
  | raised {failure : SolverAdapter.Failure} : Live bound → prunes (pruneInput operations bound source) work (.error failure) →
      Run operations prunes denotes source bound (.error failure)
        [.prune (pruneInput operations bound source)] (work + 1)
  | direct : Live bound → prunes (pruneInput operations bound source) work (.ok pruned) →
      route operations.constraints bound pruned = .returned result →
      Run operations prunes denotes source bound (.ok (result.map operations.grouped))
        [.prune (pruneInput operations bound source)] (work + 1)
  | fallback {guard : SourceGuards.Guard Formula} : Live bound → prunes (pruneInput operations bound source) pruneWork (.ok pruned) →
      route operations.constraints bound pruned = .denoted depth guard →
      denotes depth source denoteWork accepted →
      Run operations prunes denotes source bound
        (accepted.map (finish operations.rebuild operations.grouped guard))
        [.prune (pruneInput operations bound source), .denotation depth source] (pruneWork + denoteWork + 1)

variable (operations : Operations Formula Graph Term BuildError Value)
  (prunes : Graph → Nat → Except SolverAdapter.Failure (Except (PruneError Unknown Invalid) Graph) → Prop)
  (denotes : Int → Graph → Nat → Except SolverAdapter.Failure (Except DenotationUnknown (List Term)) → Prop)

/-- All source executions make at most one pruning call and one denotation call. -/
theorem calls_bounded {source bound result calls work}
    (run : Run operations prunes denotes source bound result calls work) : calls.length ≤ 2 := by
  cases run <;> simp

/-- Negative bounds return an empty generator with no calls, for every possible backend. -/
theorem negative_exact {source depth result calls work} (negative : depth < 0)
    (run : Run operations prunes denotes source (some depth) result calls work) :
    result = .ok (.ok operations.empty) ∧ calls = [] ∧ work = 1 := by
  cases run with
  | negative => exact ⟨rfl, rfl, rfl⟩
  | raised live _ | direct live _ _ | fallback live _ _ _ =>
      have := live depth rfl
      omega

/-- The fallback trace identifies the original graph and the nonnegative requested bound. -/
theorem fallback_origin {source bound result work input depth graph}
    (run : Run operations prunes denotes source bound result
      [.prune input, .denotation depth graph] work) :
    graph = source ∧ bound = some depth ∧ 0 ≤ depth ∧
      input = operations.boundDepth depth source ∧
      ∃ pruneWork reduced guard,
        prunes input pruneWork (.ok (.ok reduced)) ∧
        scan (operations.constraints reduced) = .error guard := by
  cases run with
  | fallback live pruned routed accepted =>
      obtain ⟨reduced, same, boundEq, failed⟩ := (route_denoted_iff _ _ _ _ _).mp routed
      subst same
      refine ⟨rfl, boundEq, live _ boundEq, ?_, _, reduced, _, pruned, failed⟩
      simp [pruneInput, boundEq]

/-- Successful direct imports retain a successfully scanned reduced graph. -/
theorem direct_success {source bound output work input}
    (run : Run operations prunes denotes source bound (.ok (.ok output)) [.prune input] work) :
    ∃ reduced pruneWork, prunes input pruneWork (.ok (.ok reduced)) ∧
      scan (operations.constraints reduced) = .ok () ∧ operations.grouped reduced = output := by
  generalize resultEq : (Except.ok (.ok output) : Except SolverAdapter.Failure (Except (Error Formula Invalid) Value)) = result at run
  cases run with
  | raised live pruned => cases resultEq
  | direct live pruned routed =>
      rename_i result
      cases result with
      | error error => cases resultEq
      | ok reduced =>
          obtain ⟨same, scanned⟩ := (route_success _ _ _ _).mp routed
          subst same
          exact ⟨reduced, _, pruned, scanned, (Except.ok.inj (Except.ok.inj resultEq)).symm⟩

/-- A successful fallback was built from the completed denotation of the original graph. -/
theorem fallback_success {source bound output work input depth graph}
    (run : Run operations prunes denotes source bound (.ok (.ok output))
      [.prune input, .denotation depth graph] work) :
    ∃ denoteWork terms rebuilt,
      denotes depth source denoteWork (.ok (.ok terms)) ∧
      operations.rebuild terms = .ok rebuilt ∧ operations.grouped rebuilt = output := by
  generalize resultEq : (Except.ok (.ok output) : Except SolverAdapter.Failure (Except (Error Formula Invalid) Value)) = result at run
  cases run with
  | fallback live pruned routed denoted =>
      rename_i accepted guard
      cases accepted with
      | error failure => cases resultEq
      | ok accepted =>
          obtain ⟨terms, rebuilt, same, built, outputEq⟩ :=
            (finish_success operations.rebuild operations.grouped _ accepted _).mp (Except.ok.inj resultEq).symm
          subst same
          exact ⟨_, terms, rebuilt, denoted, built, outputEq⟩

/-- Finite completed external calls suffice for the finite import control path. -/
theorem finite (pruneCompletes : ∀ graph, ∃ work result, prunes graph work result)
    (denotationCompletes : ∀ depth graph, 0 ≤ depth → ∃ work result, denotes depth graph work result)
    (source : Graph) (bound : Option Int) :
    ∃ result calls work, Run operations prunes denotes source bound result calls work := by
  by_cases live : Live bound
  · obtain ⟨pruneWork, result, pruned⟩ := pruneCompletes (pruneInput operations bound source)
    cases result with
    | error failure => exact ⟨_, _, _, .raised live pruned⟩
    | ok prunedGraph =>
        cases routed : route operations.constraints bound prunedGraph with
        | returned result => exact ⟨_, _, _, .direct live pruned routed⟩
        | denoted depth guard =>
            obtain ⟨_, _, boundEq, _⟩ := (route_denoted_iff _ _ _ _ _).mp routed
            obtain ⟨denoteWork, accepted, denoted⟩ := denotationCompletes depth source (live _ boundEq)
            exact ⟨_, _, _, .fallback live pruned routed denoted⟩
  · cases bound with
    | none => exact False.elim (live (by simp [Live]))
    | some depth =>
        have negative : depth < 0 := by simpa [Live] using live
        exact ⟨_, _, _, .negative negative⟩

end MicroCFTA.SourceCompileImportExecution
