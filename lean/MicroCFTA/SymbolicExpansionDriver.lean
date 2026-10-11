import MicroCFTA.SymbolicEdgeCounts

/-!
# Correctness of the source variable-expansion branch

The proof follows the actual stateful union loop and indicator loop.
Its recursive premise applies to smaller `solve` calls. All finite-count
identities and the fresh binding invariant are derived here.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- The exact expansion update satisfies the recursive normalizer's binding invariant. -/
theorem expandedProblem_admissible (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (empty : problem.bindings = [])
    (fresh : ∀ entry ∈ problem.domains, entry.1 < problem.nextVariable)
    (name node : Nat) (selected : (name, node) ∈ problem.domains) (edge : Edge Symbol)
    (classes : List (List (List Nat))) :
    ((expandedProblem problem name edge classes).domains.map Prod.fst).Nodup ∧
      AdmissibleBindings (expandedProblem problem name edge classes) := by
  refine ⟨expand_variables_fresh problem.domains distinct name problem.nextVariable edge.children fresh, Or.inr ?_⟩
  refine ⟨name, expansionContext problem edge, ?_, ?_, ?_⟩
  · simp [expandedProblem, empty, insert, delete]
  · intro present
    obtain ⟨entry, member, same⟩ := List.mem_map.mp present
    rcases (expanded_domain_member problem name edge classes entry).mp member with new | old
    · have inRange := (List.of_mem_zip new).1
      obtain ⟨offset, _, equal⟩ := List.mem_range'.mp inRange
      have bound := fresh (name, node) selected
      omega
    · exact old.2 same
  · exact expansion_binding_acyclic name problem.nextVariable edge.symbol edge.children.length (fresh (name, node) selected)

/-- A successful source expansion returns the exact problem count and preserves its cache invariant. -/
theorem expandVariable_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (distinct : ∀ node, (language node).Nodup)
    (invariant : Counts Symbol → Prop) (fuel : Nat)
    (recursive : ∀ problem before count after,
      (problem.domains.map Prod.fst).Nodup → AdmissibleBindings problem → invariant before →
      solve graph fuel problem before = .ok (count, after) →
        count = (solutionCount language problem : Int) ∧ invariant after)
    (problem : Problem Symbol) (namesDistinct : (problem.domains.map Prod.fst).Nodup)
    (empty : problem.bindings = []) (within : ProblemScoped problem)
    (fresh : ∀ entry ∈ problem.domains, entry.1 < problem.nextVariable)
    (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (exact : ∀ term, Symbolic.weighted
      (fun component => Lattice.indicator (@decide (term ∈ componentTerms language component.1 component.2) (Classical.propDecidable _)))
      (expansionPieces graph node) = Lattice.indicator (@decide (term ∈ language node) (Classical.propDecidable _)))
    (before after : Counts Symbol) (result : Int) (starts : invariant before)
    (success : expandVariable graph (fuel + 1) problem name before = .ok (result, after)) :
    result = (solutionCount language problem : Int) ∧ invariant after := by
  classical
  let action := fun edge : Edge Symbol => (do
    let values ← edge.indicators.mapM fun (coefficient, classes) => do
      let count ← solve graph fuel (expandedProblem problem name edge classes)
      pure (coefficient * count)
    pure values.sum : CountM Symbol Int)
  let meaning := fun edge : Edge Symbol => (edge.indicators.map fun (coefficient, classes) =>
    coefficient * (solutionCount language (expandedProblem problem name edge classes) : Int)).sum
  have correct : ∀ edge before count after, invariant before →
      action edge before = .ok (count, after) → count = meaning edge ∧ invariant after := by
    intro edge initial count finalState good succeeds
    let part := fun piece : Int × List (List (List Nat)) => (do
      let amount ← solve graph fuel (expandedProblem problem name edge piece.2)
      pure (piece.1 * amount) : CountM Symbol Int)
    let value := fun piece : Int × List (List (List Nat)) => piece.1 * (solutionCount language (expandedProblem problem name edge piece.2) : Int)
    have partCorrect : ∀ piece initial amount finalState, invariant initial →
        part piece initial = .ok (amount, finalState) → amount = value piece ∧ invariant finalState := by
      intro piece state amount finalCache valid solved
      change Except.bind (solve graph fuel (expandedProblem problem name edge piece.2) state)
        (fun (subtotal, cache) => .ok (piece.1 * subtotal, cache)) = .ok (amount, finalCache) at solved
      cases computed : solve graph fuel (expandedProblem problem name edge piece.2) state with
      | error error => simp only [computed] at solved; cases solved
      | ok pair =>
          obtain ⟨subtotal, cache⟩ := pair
          have admissible := expandedProblem_admissible problem namesDistinct empty fresh name node selected edge piece.2
          have verified := recursive (expandedProblem problem name edge piece.2) state subtotal cache
            admissible.1 admissible.2 valid computed
          simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at solved
          obtain ⟨rfl, rfl⟩ := solved
          exact ⟨by simp only [value, verified.1], verified.2⟩
    change Except.bind ((edge.indicators.mapM part : CountM Symbol (List Int)) initial)
      (fun (values, cache) => .ok (values.sum, cache)) = .ok (count, finalState) at succeeds
    cases computed : (edge.indicators.mapM part : CountM Symbol (List Int)) initial with
    | error error => simp only [computed] at succeeds; cases succeeds
    | ok pair =>
        obtain ⟨values, cache⟩ := pair
        have verified := state_mapM_correct part value invariant partCorrect edge.indicators initial cache values good computed
        simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at succeeds
        obtain ⟨rfl, rfl⟩ := succeeds
        exact ⟨by rw [verified.1], verified.2⟩
  have found : domain problem name = .ok node := by
    simp only [domain, lookup_of_member problem.domains namesDistinct name node selected]
  have unionSuccess : countUnion graph action (graph.edges node) before = .ok (result, after) := by
    simpa only [expandVariable, found, action, expandedProblem, expansionContext, Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift,
      StateT.lift, Pure.pure, Except.pure, Except.bind] using success
  have verified := countUnion_correct graph action meaning invariant correct (graph.edges node) before after result starts unionSuccess
  refine ⟨verified.1.trans ?_, verified.2⟩
  apply expand_variable_count graph language distinct problem namesDistinct empty within fresh name node selected
  intro term
  simpa only [Lattice.indicator, decide_eq_true_eq] using exact term

end MicroCFTA.SymbolicDriver
