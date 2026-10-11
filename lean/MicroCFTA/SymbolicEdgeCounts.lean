import MicroCFTA.SymbolicSignedSolutions

/-!
# Initial edge problems and their exact finite counts

The source counter builds one live child domain for each child position.
Its constructor context reads those positions in the original order.
This module relates that exact problem to each raw equality component.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment instantiate instantiateMany Satisfies)

/-- The source's constructor context at entry to `countEdge`. -/
def edgeContext (edge : Edge Symbol) : Fragment Symbol :=
  .constructor edge.symbol ((List.range edge.children.length).map Fragment.var)

/-- The exact source problem for one raw equality indicator of an edge. -/
def edgeProblem (edge : Edge Symbol) (classes : List (List (List Nat))) : Problem Symbol :=
  ⟨edge.children.zipIdx.map (fun (node, name) => (name, node)), [], edge.children.length,
    Symbolic.edgeObligations (edgeContext edge) classes⟩

/-- Initial edge domains preserve the original ordered child graph identities. -/
theorem edgeProblem_graphs (edge : Edge Symbol) (classes : List (List (List Nat))) :
    ((edgeProblem edge classes).domains.map Prod.snd) = edge.children := by
  simp only [edgeProblem, List.map_map, Function.comp_def]
  exact List.zipIdx_map_fst 0 edge.children

/-- Initial edge names are exactly the consecutive child positions. -/
theorem edgeProblem_names (edge : Edge Symbol) (classes : List (List (List Nat))) :
    ((edgeProblem edge classes).domains.map Prod.fst) = List.range edge.children.length := by
  simp only [edgeProblem, List.map_map, Function.comp_def, List.range_eq_range']
  exact List.zipIdx_map_snd 0 edge.children

/-- Initial edge problems satisfy the normalizer's distinct-domain and binding assumptions. -/
theorem edgeProblem_admissible (edge : Edge Symbol) (classes : List (List (List Nat))) :
    ((edgeProblem edge classes).domains.map Prod.fst).Nodup ∧ AdmissibleBindings (edgeProblem edge classes) := by
  exact ⟨by rw [edgeProblem_names]; exact List.nodup_range, Or.inl rfl⟩

/-- A matching live tuple instantiates to the constructor with that exact child tuple. -/
theorem edgeContext_matching (edge : Edge Symbol) (classes : List (List (List Nat)))
    (assignment : Nat → Term Symbol) (values : List (Term Symbol))
    (matching : TupleMatches assignment (edgeProblem edge classes).domains values) :
    instantiate assignment (edgeContext edge) = .node edge.symbol values := by
  have equal := (tupleMatches_iff assignment (edgeProblem edge classes).domains values).mp matching
  have mapped : (List.range edge.children.length).map assignment = values := by
    rw [← edgeProblem_names edge classes, List.map_map]
    exact equal.symm
  simp only [edgeContext, instantiate, instantiate_variables, mapped]

/-- The initial problem's logical solution test is exactly the edge's equality conjunction. -/
theorem edgeProblem_live (language : Nat → List (Term Symbol)) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (values : List (Term Symbol))
    (candidate : values ∈ candidateTuples language (edgeProblem edge classes).domains) :
    LiveSolution (edgeProblem edge classes) values ↔
      ∀ paths ∈ classes, Symbolic.ClassSatisfied (.node edge.symbol values) paths := by
  constructor
  · rintro ⟨assignment, matching, _, constraints⟩
    have guards := (Symbolic.edgeObligations_correct (edgeContext edge) assignment classes).mp constraints
    simpa only [edgeContext_matching edge classes assignment values matching] using guards
  · intro guards
    obtain ⟨assignment, matching⟩ := tuple_assignment_exists (.node edge.symbol [])
      (edgeProblem edge classes).domains values (edgeProblem_admissible edge classes).1
      (candidate_tuple_length language (edgeProblem edge classes).domains values candidate)
    refine ⟨assignment, matching, ?_, ?_⟩
    · simp [BindingsHold, edgeProblem]
    · exact (Symbolic.edgeObligations_correct (edgeContext edge) assignment classes).mpr
        (by simpa only [edgeContext_matching edge classes assignment values matching] using guards)

/-- The exact initial edge problem counts its component's distinct constructor terms. -/
theorem edgeProblem_count (language : Nat → List (Term Symbol)) (edge : Edge Symbol)
    (classes : List (List (List Nat))) :
    solutionCount language (edgeProblem edge classes) = (componentTerms language edge classes).length := by
  classical
  have filtered : solutionTuples language (edgeProblem edge classes) =
      (candidateTuples language (edgeProblem edge classes).domains).filter fun values =>
        decide (∀ paths ∈ classes, Symbolic.ClassSatisfied (.node edge.symbol values) paths) := by
    unfold solutionTuples
    apply List.filter_congr
    intro values member
    simp only [edgeProblem_live language edge classes values member]
  rw [solutionCount, filtered]
  simp only [candidateTuples, edgeProblem_graphs, componentTerms, List.filter_map, List.length_map]
  rfl

/-- The source's signed edge count is the sum of the raw component cardinalities. -/
noncomputable def semanticEdgeCount (language : Nat → List (Term Symbol)) (edge : Edge Symbol) : Int :=
  (edge.indicators.map fun (coefficient, classes) => coefficient * ((componentTerms language edge classes).length : Int)).sum

/-- Correct recursive problem counts imply the actual `countEdge` result and cache preservation. -/
theorem countEdge_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (invariant : Counts Symbol → Prop) (fuel : Nat)
    (recursive : ∀ problem before count after,
      (problem.domains.map Prod.fst).Nodup → AdmissibleBindings problem → invariant before →
      solve graph fuel problem before = .ok (count, after) →
        count = (solutionCount language problem : Int) ∧ invariant after)
    (edge : Edge Symbol) (before after : Counts Symbol) (result : Int) (starts : invariant before)
    (success : countEdge graph (fuel + 1) edge before = .ok (result, after)) :
    result = semanticEdgeCount language edge ∧ invariant after := by
  let action := fun piece : Int × List (List (List Nat)) => (do
    let count ← solve graph fuel (edgeProblem edge piece.2)
    pure (piece.1 * count) : CountM Symbol Int)
  let value := fun piece : Int × List (List (List Nat)) => piece.1 * ((componentTerms language edge piece.2).length : Int)
  have correct : ∀ piece before count after, invariant before →
      action piece before = .ok (count, after) → count = value piece ∧ invariant after := by
    intro piece initial count finalState good succeeds
    change Except.bind (solve graph fuel (edgeProblem edge piece.2) initial)
      (fun (amount, state) => .ok (piece.1 * amount, state)) = .ok (count, finalState) at succeeds
    cases computed : solve graph fuel (edgeProblem edge piece.2) initial with
    | error error => simp only [computed] at succeeds; cases succeeds
    | ok pair =>
        obtain ⟨amount, state⟩ := pair
        have verified := recursive (edgeProblem edge piece.2) initial amount state
          (edgeProblem_admissible edge piece.2).1 (edgeProblem_admissible edge piece.2).2 good computed
        simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at succeeds
        obtain ⟨rfl, rfl⟩ := succeeds
        exact ⟨by simp only [value, verified.1, edgeProblem_count], verified.2⟩
  change Except.bind ((edge.indicators.mapM action : CountM Symbol (List Int)) before)
    (fun (values, state) => .ok (values.sum, state)) = .ok (result, after) at success
  cases computed : (edge.indicators.mapM action : CountM Symbol (List Int)) before with
  | error error => simp only [computed] at success; cases success
  | ok pair =>
      obtain ⟨values, state⟩ := pair
      have verified := state_mapM_correct action value invariant correct edge.indicators before state values starts computed
      simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨by simp only [verified.1]; rfl, verified.2⟩

end MicroCFTA.SymbolicDriver
