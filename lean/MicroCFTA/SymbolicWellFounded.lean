import MicroCFTA.SymbolicCallProgress

/-!
# A well-founded call relation for the source counter

The relation records every recursive control branch. Cache hits, empty
results, and rejected equations make no recursive call. Solve calls carry
the finite substitution budget justified by their caller invariant.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation)

/-- Control locations of the six source functions. -/
inductive CounterCall (Symbol : Type) where
  | node : Nat → CounterCall Symbol
  | edge : Edge Symbol → CounterCall Symbol
  | solve : Problem Symbol → (Nat → Nat) → CounterCall Symbol
  | step : Problem Symbol → CounterCall Symbol
  | unify : Problem Symbol → Fragment Symbol → Fragment Symbol → CounterCall Symbol
  | expand : Problem Symbol → Nat → CounterCall Symbol

/-- The constructor-variable orientation has one extra control phase for the source swap. -/
def unifyPhase : Fragment Symbol → Fragment Symbol → Nat
  | .constructor _ _, .var _ => 3
  | _, _ => 2

/-- Lexicographic structural-domain, pending-work, and control-phase measure. -/
def callMeasure (budget : Nat → Nat) : CounterCall Symbol → Nat × (Nat × Nat)
  | .node node => (budget node, (0, 0))
  | .edge edge => ((edge.children.map budget).sum,
      ((edge.indicators.map fun piece => obligationsWork (fun _ => 1) (edgeProblem edge piece.2).obligations).sum + 1, 6))
  | .solve problem weight => (domainBudget budget problem.domains, (obligationsWork weight problem.obligations, 5))
  | .step problem => (domainBudget budget problem.domains, (obligationsWork (fun _ => 1) problem.obligations, 4))
  | .unify problem left right => (domainBudget budget problem.domains,
      (obligationsWork (fun _ => 1) (equationProblem problem left right).obligations, unifyPhase left right))
  | .expand problem _ => (domainBudget budget problem.domains, (obligationsWork (fun _ => 1) problem.obligations, 1))

/-- Recursive source calls, oriented from the called operation to its caller. -/
inductive CounterCallStep [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) : CounterCall Symbol → CounterCall Symbol → Prop where
  | nodeEdge (node : Nat) (piece : Edge Symbol × Int)
      (member : piece ∈ Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) :
      CounterCallStep graph (.edge piece.1) (.node node)
  | edgeSolve (edge : Edge Symbol) (piece : Int × List (List (List Nat))) (member : piece ∈ edge.indicators) :
      CounterCallStep graph (.solve (edgeProblem edge piece.2) (fun _ => 1)) (.edge edge)
  | solveStep (problem normalized : Problem Symbol) (weight : Nat → Nat) (fuel : Nat)
      (budget : BindingBudget weight problem.bindings) (success : normalize fuel problem = .ok (some normalized)) :
      CounterCallStep graph (.step normalized) (.solve problem weight)
  | stepDomain (problem : Problem Symbol) (entry : Nat × Nat) (member : entry ∈ problem.domains) :
      CounterCallStep graph (.node entry.2) (.step problem)
  | stepExists (problem : Problem Symbol) (target : Symbolic.Target Symbol) (rest : List (Obligation Symbol))
      (pending : problem.obligations = .exists target :: rest) :
      CounterCallStep graph (.solve {problem with obligations := rest} (fun _ => 1)) (.step problem)
  | stepUnify (problem : Problem Symbol) (left right : Symbolic.Target Symbol) (first second : Fragment Symbol)
      (rest : List (Obligation Symbol)) (pending : problem.obligations = .equal left right :: rest)
      (leftFound : Symbolic.resolveContext left.fragment left.path = .resolved first)
      (rightFound : Symbolic.resolveContext right.fragment right.path = .resolved second) :
      CounterCallStep graph (.unify {problem with obligations := rest} first second) (.step problem)
  | stepExpand (problem : Problem Symbol) (name : Nat) : CounterCallStep graph (.expand problem name) (.step problem)
  | unifySame (problem : Problem Symbol) (name : Nat) :
      CounterCallStep graph (.solve problem (fun _ => 1)) (.unify problem (.var name) (.var name))
  | unifyMerge (problem : Problem Symbol) (left right leftNode rightNode : Nat) (weight : Nat → Nat)
      (distinct : (problem.domains.map Prod.fst).Nodup) (different : left ≠ right)
      (leftMember : (left, leftNode) ∈ problem.domains) (rightMember : (right, rightNode) ∈ problem.domains) :
      CounterCallStep graph (.solve (mergedProblem problem left right (graph.intersect leftNode rightNode)) weight)
        (.unify problem (.var left) (.var right))
  | unifyExpand (problem : Problem Symbol) (name : Nat) (symbol : Symbol) (children : List (Fragment Symbol)) :
      CounterCallStep graph (.expand (equationProblem problem (.var name) (.constructor symbol children)) name)
        (.unify problem (.var name) (.constructor symbol children))
  | unifySwap (problem : Problem Symbol) (name : Nat) (symbol : Symbol) (children : List (Fragment Symbol)) :
      CounterCallStep graph (.unify problem (.var name) (.constructor symbol children))
        (.unify problem (.constructor symbol children) (.var name))
  | unifyChildren (problem : Problem Symbol) (symbol : Symbol) (children others : List (Fragment Symbol))
      (arity : children.length = others.length) :
      CounterCallStep graph (.solve {problem with
          obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations} (fun _ => 1))
        (.unify problem (.constructor symbol children) (.constructor symbol others))
  | expandSolve (problem : Problem Symbol) (name node : Nat) (piece : Edge Symbol × Int)
      (classes : List (List (List Nat))) (weight : Nat → Nat)
      (distinct : (problem.domains.map Prod.fst).Nodup) (selected : (name, node) ∈ problem.domains)
      (member : piece ∈ Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) :
      CounterCallStep graph (.solve (expandedProblem problem name piece.1 classes) weight) (.expand problem name)

/-- Each stored value is bounded by the complete nonnegative sum. -/
theorem member_sum_bound (measure : Value → Nat) (values : List Value) (value : Value) (member : value ∈ values) :
    measure value ≤ (values.map measure).sum := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.map_cons, List.sum_cons]; omega
      · have bound := ih member
        simp only [List.map_cons, List.sum_cons]; omega

/-- Every recursive source control branch decreases the explicit lexicographic measure. -/
theorem counter_call_decreases [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (budget : SourceBudget graph)
    (child parent : CounterCall Symbol) (step : CounterCallStep graph child parent) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (callMeasure budget.value child) (callMeasure budget.value parent) := by
  cases step with
  | nodeEdge node piece member =>
      exact Prod.Lex.left _ _ (union_edge_budget graph budget node piece member)
  | edgeSolve edge piece member =>
      have domains : domainBudget budget.value (edgeProblem edge piece.2).domains = (edge.children.map budget.value).sum := by
        have same := congrArg (List.map budget.value) (edgeProblem_graphs edge piece.2)
        simpa only [domainBudget, List.map_map, Function.comp_def] using congrArg List.sum same
      apply Prod.lex_def.mpr
      refine Or.inr ⟨domains, Prod.Lex.left _ _ ?_⟩
      have bound := member_sum_bound (fun part : Int × List (List (List Nat)) =>
        obligationsWork (fun _ => 1) (edgeProblem edge part.2).obligations) edge.indicators piece member
      change obligationsWork (fun _ => 1) (edgeProblem edge piece.2).obligations <
        (edge.indicators.map fun part => obligationsWork (fun _ => 1) (edgeProblem edge part.2).obligations).sum + 1
      omega
  | solveStep problem normalized weight fuel bindingBudget success =>
      apply Prod.lex_def.mpr
      refine Or.inr ⟨normalize_preserves_budget budget.value fuel problem normalized success, ?_⟩
      exact Prod.Lex.right' Nat.lt (normalize_work weight problem bindingBudget fuel normalized success) (by decide : 4 < 5)
  | stepDomain problem entry member =>
      exact Prod.Lex.right' (Prod.Lex Nat.lt Nat.lt) (member_sum_bound (fun item : Nat × Nat => budget.value item.2) problem.domains entry member)
        (Prod.Lex.right' Nat.lt (Nat.zero_le _) (by decide : 0 < 4))
  | stepExists problem target rest pending =>
      apply Prod.Lex.right
      apply Prod.Lex.left
      change obligationsWork (fun _ => 1) rest < obligationsWork (fun _ => 1) problem.obligations
      rw [pending]
      exact drop_obligation_progress (.exists target) rest
  | stepUnify problem left right first second rest pending leftFound rightFound =>
      apply Prod.Lex.right
      apply Prod.Lex.right' Nat.lt
      · have leftBound := resolved_context_work left.fragment left.path first leftFound
        have rightBound := resolved_context_work right.fragment right.path second rightFound
        simp only [equationProblem, pending, obligationsWork, List.map_cons, List.sum_cons,
          obligationWork, targetWork, List.length_nil, Nat.add_zero]
        omega
      · cases first <;> cases second <;> simp [unifyPhase, Nat.lt]
  | stepExpand problem name => exact Prod.Lex.right _ (Prod.Lex.right _ (by decide : 1 < 4))
  | unifySame problem name =>
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact drop_obligation_progress (.equal ⟨.var name, []⟩ ⟨.var name, []⟩) problem.obligations
  | unifyMerge problem left right leftNode rightNode weight distinct different leftMember rightMember =>
      exact Prod.Lex.left _ _ (unify_variables_progress budget.value problem.domains distinct left right leftNode rightNode
        (graph.intersect leftNode rightNode) different leftMember rightMember (budget.positive leftNode)
        (budget.intersection leftNode rightNode).2)
  | unifyExpand problem name symbol children => exact Prod.Lex.right _ (Prod.Lex.right _ (by decide : 1 < 2))
  | unifySwap problem name symbol children =>
      apply Prod.Lex.right
      apply Prod.lex_def.mpr
      refine Or.inr ⟨?_, ?_⟩
      · simp only [equationProblem, obligationsWork, List.map_cons, List.sum_cons, obligationWork,
          targetWork, List.length_nil, Nat.add_zero, fragmentWork]
        omega
      · change 2 < 3
        decide
  | unifyChildren problem symbol children others arity =>
      exact Prod.Lex.right _ (Prod.Lex.left _ _ (constructor_children_progress problem symbol children others arity))
  | expandSolve problem name node piece classes weight distinct selected member =>
      exact Prod.Lex.left _ _ (expand_variable_progress budget.value problem.domains distinct name node problem.nextVariable piece.1.children
        selected (union_edge_budget graph budget node piece member))

/-- The complete source counter call relation has no infinite descending chain under structural graph budgets. -/
theorem counter_calls_wellFounded [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (budget : SourceBudget graph) :
    WellFounded (CounterCallStep graph) := by
  have lexicographic : WellFounded (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) :=
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf
  exact Subrelation.wf (fun step => counter_call_decreases graph budget _ _ step)
    (InvImage.wf (callMeasure budget.value) lexicographic)

end MicroCFTA.SymbolicDriver
