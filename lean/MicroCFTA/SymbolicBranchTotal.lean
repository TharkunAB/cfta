import MicroCFTA.SymbolicEventual

/-!
# Stable successful bounds for source counter branches

These lemmas compose the exact source operations from eventual recursive
results. The bounds preserve the complete output cache, so later calls can
reuse one common fuel bound.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation)

/-- Every node branch eventually succeeds when all generated edge calls do. -/
theorem countNode_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (node : Nat)
    (recursive : ∀ piece ∈ Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node), ∀ state,
      Eventually (fun fuel => countEdge graph fuel piece.1) state) (initial : Counts Symbol) :
    Eventually (fun fuel => countNode graph fuel node) initial := by
  by_cases empty : (graph.edges node).isEmpty = true
  · refine ⟨1, 0, initial, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp only [countNode, empty, ite_true]; rfl
  · have nonempty : (graph.edges node).isEmpty = false := Bool.eq_false_iff.mpr empty
    cases cached : lookup initial.graphs node with
    | some count =>
        refine ⟨1, count, initial, ?_⟩
        intro fuel bound
        cases fuel with
        | zero => omega
        | succ fuel => exact countNode_cached graph fuel node initial count nonempty cached
    | none =>
        obtain ⟨bound, count, finalState, stable⟩ :=
          countUnion_eventually graph (fun fuel => countEdge graph fuel) (graph.edges node) recursive initial
        dsimp only at stable
        refine ⟨bound + 1, count, {finalState with graphs := insert finalState.graphs node count}, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [countNode, nonempty, Bool.false_eq_true, ite_false, Bind.bind, StateT.bind,
              get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure, Except.bind, cached]
            change Except.bind (countUnion graph (countEdge graph fuel) (graph.edges node) initial)
              (fun (value, cache) => .ok (value, {cache with graphs := insert cache.graphs node value})) = _
            rw [stable fuel (by omega)]
            rfl

/-- Every signed edge loop eventually succeeds when each initial component problem does. -/
theorem countEdge_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (edge : Edge Symbol)
    (recursive : ∀ piece ∈ edge.indicators, ∀ state,
      Eventually (fun fuel => solve graph fuel (edgeProblem edge piece.2)) state) (initial : Counts Symbol) :
    Eventually (fun fuel => countEdge graph fuel edge) initial := by
  let action := fun fuel (piece : Int × List (List (List Nat))) => (do
    let count ← solve graph fuel (edgeProblem edge piece.2)
    pure (piece.1 * count) : CountM Symbol Int)
  have total : Eventually (fun fuel => edge.indicators.mapM (action fuel)) initial := by
    apply eventually_mapM
    intro piece member state
    exact eventually_bind _ _ state (recursive piece member state) (fun count cache => eventually_pure (piece.1 * count) cache)
  obtain ⟨bound, values, finalState, stable⟩ := total
  dsimp only at stable
  refine ⟨bound + 1, values.sum, finalState, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel =>
      change Except.bind ((edge.indicators.mapM (action fuel) : CountM Symbol (List Int)) initial)
        (fun (values, cache) => .ok (values.sum, cache)) = _
      rw [stable fuel (by omega)]
      rfl

/-- The source normalizer and context memo path eventually succeed when each normalized step does. -/
theorem solve_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (problem : Problem Symbol)
    (weight : Nat → Nat) (budget : BindingBudget weight problem.bindings) (within : InputScope problem)
    (recursive : ∀ normalized fuel, normalize fuel problem = .ok (some normalized) → ∀ state,
      Eventually (fun bound => solveStep graph bound normalized) state) (initial : Counts Symbol) :
    Eventually (fun fuel => solve graph fuel problem) initial := by
  by_cases empty : problem.domains.any (fun entry => (graph.edges entry.2).isEmpty) = true
  · refine ⟨1, 0, initial, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp only [solve, empty, ite_true]; rfl
  · have nonempty : problem.domains.any (fun entry => (graph.edges entry.2).isEmpty) = false := Bool.eq_false_iff.mpr empty
    let normalizeBound := 2 * obligationsWork weight problem.obligations + 1
    obtain ⟨normalized, normalization⟩ := scoped_normalize_total problem weight budget within normalizeBound (Nat.le_refl _)
    have normalStable : ∀ fuel, normalizeBound ≤ fuel → normalize fuel problem = .ok normalized :=
      fun fuel bound => normalize_fuel_mono problem normalizeBound fuel bound normalized normalization
    cases normalized with
    | none =>
        refine ⟨normalizeBound + 1, 0, initial, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [solve, nonempty, Bool.false_eq_true, ite_false, normalStable (fuel + 1) (by omega),
              Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, Pure.pure, Except.pure, Except.bind]
            rfl
    | some current =>
        let key : Key Symbol := ⟨current.domains, current.obligations⟩
        cases cached : initial.contexts.find? (fun entry => keyEq entry.1 key) with
        | some entry =>
            obtain ⟨stored, count⟩ := entry
            refine ⟨normalizeBound + 1, count, initial, ?_⟩
            intro fuel enough
            cases fuel with
            | zero => omega
            | succ fuel =>
                dsimp only [key] at cached
                simp only [solve, nonempty, Bool.false_eq_true, ite_false, normalStable (fuel + 1) (by omega),
                  Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, Pure.pure, Except.pure,
                  get, getThe, MonadStateOf.get, StateT.get, Except.bind, cached]
                rfl
        | none =>
            obtain ⟨stepBound, count, finalState, stable⟩ := recursive current normalizeBound normalization initial
            dsimp only at stable
            refine ⟨max normalizeBound stepBound + 1, count, {finalState with contexts := (key, count) :: finalState.contexts}, ?_⟩
            intro fuel enough
            cases fuel with
            | zero => omega
            | succ fuel =>
                dsimp only [key] at cached
                simp only [solve, nonempty, Bool.false_eq_true, ite_false, normalStable (fuel + 1) (by omega),
                  Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, Pure.pure, Except.pure,
                  get, getThe, MonadStateOf.get, StateT.get, Except.bind, cached]
                change Except.bind (solveStep graph fuel current initial)
                  (fun (value, cache) => .ok (value, {cache with contexts := (key, value) :: cache.contexts})) = _
                rw [stable fuel (by omega)]
                rfl

end MicroCFTA.SymbolicDriver
