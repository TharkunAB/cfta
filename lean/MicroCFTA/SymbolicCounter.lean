import MicroCFTA.SymbolicUnification

/-!
# Mutual semantic correctness of the source symbolic counter

The six predicates below are induction statements for the six executable
source functions. They use exact finite live-tuple counts and the semantic
cache invariant. The graph interface contains no counter-correctness premise.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation Satisfies)

/-- Correct graph counts for all successful calls at one execution bound. -/
def NodeCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ node before count after, SemanticCache language before →
    countNode graph fuel node before = .ok (count, after) →
      count = ((language node).length : Int) ∧ SemanticCache language after

/-- Correct signed edge counts for all successful calls at one execution bound. -/
def EdgeCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ edge before count after, SemanticCache language before →
    countEdge graph fuel edge before = .ok (count, after) →
      count = semanticEdgeCount language edge ∧ SemanticCache language after

/-- Correct finite problem counts for the substitution shapes used by recursive callers. -/
def SolveCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ problem before count after, (problem.domains.map Prod.fst).Nodup → AdmissibleBindings problem →
    SemanticCache language before → solve graph fuel problem before = .ok (count, after) →
      count = (solutionCount language problem : Int) ∧ SemanticCache language after

/-- Correct normalized solver steps. -/
def StepCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ problem before count after, NormalProblem problem → SemanticCache language before →
    solveStep graph fuel problem before = .ok (count, after) →
      count = (solutionCount language problem : Int) ∧ SemanticCache language after

/-- Correct whole-context unification for scoped input contexts. -/
def UnifyCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ problem left right before count after, NormalProblem problem →
    InScope (fun name => name ∈ problem.domains.map Prod.fst) left →
    InScope (fun name => name ∈ problem.domains.map Prod.fst) right →
    SemanticCache language before → unify graph fuel problem left right before = .ok (count, after) →
      count = (solutionCount language (equationProblem problem left right) : Int) ∧ SemanticCache language after

/-- Correct expansion at a live name of a normalized problem. -/
def ExpandCorrect [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (fuel : Nat) : Prop :=
  ∀ problem name before count after, NormalProblem problem → name ∈ problem.domains.map Prod.fst →
    SemanticCache language before → expandVariable graph fuel problem name before = .ok (count, after) →
      count = (solutionCount language problem : Int) ∧ SemanticCache language after

/-- A scoped variable has exactly one stored live domain. -/
theorem scoped_variable_domain (problem : Problem Symbol) (name : Nat)
    (within : InScope (fun key => key ∈ problem.domains.map Prod.fst) (Fragment.var (Symbol := Symbol) name)) :
    ∃ node, (name, node) ∈ problem.domains := by
  have member := within name (by simp [occurs])
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  exact ⟨entry.2, by simpa only [← same] using entryMember⟩

/-- The actual source unifier preserves finite counts and both cache invariants in every branch. -/
theorem unify_correct_step [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fuel : Nat) (solveInduction : SolveCorrect graph meaning.terms fuel)
    (unifyInduction : UnifyCorrect graph meaning.terms fuel) (expandInduction : ExpandCorrect graph meaning.terms fuel) :
    UnifyCorrect graph meaning.terms (fuel + 1) := by
  intro problem left right before count after normal leftScope rightScope starts success
  cases left with
  | var left =>
      cases right with
      | var right =>
          by_cases same : left = right
          · subst right
            simp only [unify, ite_true] at success
            have correct := solveInduction problem before count after normal.1 (Or.inl normal.2.1) starts success
            exact ⟨by rw [equation_reflexive_count]; exact correct.1, correct.2⟩
          · obtain ⟨leftNode, leftMember⟩ := scoped_variable_domain problem left leftScope
            obtain ⟨rightNode, rightMember⟩ := scoped_variable_domain problem right rightScope
            have leftFound : domain problem left = .ok leftNode := by
              simp only [domain, lookup_of_member problem.domains normal.1 left leftNode leftMember]
            have rightFound : domain problem right = .ok rightNode := by
              simp only [domain, lookup_of_member problem.domains normal.1 right rightNode rightMember]
            have admissible := mergedProblem_admissible problem normal.1 normal.2.1 left right
              (graph.intersect leftNode rightNode) same
            have solved : solve graph fuel (mergedProblem problem left right (graph.intersect leftNode rightNode)) before = .ok (count, after) := by
              simpa only [unify, ite_eq_right same, leftFound, rightFound, Bind.bind, StateT.bind,
                liftM, monadLift, MonadLift.monadLift, StateT.lift, Pure.pure, Except.pure, Except.bind,
                mergedProblem] using success
            have correct := solveInduction _ before count after admissible.1 admissible.2 starts solved
            have counts := unify_variables_count meaning.terms meaning.distinct problem normal.1 normal.2.1
              left right leftNode rightNode (graph.intersect leftNode rightNode) leftMember rightMember
              (meaning.intersection leftNode rightNode)
            exact ⟨correct.1.trans (congrArg (fun size : Nat => (size : Int)) counts.symm), correct.2⟩
      | constructor symbol children =>
          by_cases occurrence : occurs left (.constructor symbol children) = true
          · simp only [unify, occurrence, ite_true, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
            obtain ⟨rfl, rfl⟩ := success
            have zero := occurs_solution_count meaning.terms (equationProblem problem (.var left) (.constructor symbol children))
              left symbol children problem.obligations rfl occurrence
            exact ⟨by rw [zero]; rfl, starts⟩
          · have occurrenceFalse : occurs left (.constructor symbol children) = false := Bool.eq_false_iff.mpr occurrence
            simp only [unify, occurrenceFalse, Bool.false_eq_true, ite_false] at success
            exact expandInduction (equationProblem problem (.var left) (.constructor symbol children)) left before count after
              (normal_equation problem normal (.var left) (.constructor symbol children) leftScope rightScope)
              (leftScope left (by simp [occurs])) starts success
  | constructor symbol children =>
      cases right with
      | var right =>
          have correct := unifyInduction problem (.var right) (.constructor symbol children) before count after normal rightScope leftScope starts success
          exact ⟨correct.1.trans (congrArg (fun size : Nat => (size : Int))
            (equation_symmetric_count meaning.terms problem (.var right) (.constructor symbol children))), correct.2⟩
      | constructor other others =>
          by_cases different : symbol ≠ other ∨ children.length ≠ others.length
          · simp only [unify, ite_eq_left different, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
            obtain ⟨rfl, rfl⟩ := success
            exact ⟨by rw [constructor_mismatch_count meaning.terms problem symbol other children others different]; rfl, starts⟩
          · have same : symbol = other := Classical.byContradiction (fun unequal => different (Or.inl unequal))
            have arity : children.length = others.length := Classical.byContradiction (fun unequal => different (Or.inr unequal))
            subst other
            simp only [unify, ite_eq_right different] at success
            have correct := solveInduction {problem with
              obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations}
              before count after normal.1 (Or.inl normal.2.1) starts success
            exact ⟨correct.1.trans (congrArg (fun size : Nat => (size : Int))
              (constructor_children_count meaning.terms problem symbol children others arity).symm), correct.2⟩

/-- Dropping one pending requirement retains the normalized domain and scope invariants. -/
theorem normal_tail (problem : Problem Symbol) (normal : NormalProblem problem)
    (first : Obligation Symbol) (rest : List (Obligation Symbol)) (pending : problem.obligations = first :: rest) :
    NormalProblem {problem with obligations := rest} := by
  refine ⟨normal.1, normal.2.1, normal.2.2.1, ?_⟩
  intro requirement member
  exact normal.2.2.2 requirement (by simp only [pending, List.mem_cons]; exact Or.inr member)

/-- An absent side of a path equation gives zero finite solutions. -/
theorem absent_equality_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (left right : Symbolic.Target Symbol) (rest : List (Obligation Symbol))
    (pending : problem.obligations = .equal left right :: rest)
    (missing : Symbolic.resolveContext left.fragment left.path = .absent ∨ Symbolic.resolveContext right.fragment right.path = .absent) :
    solutionCount language problem = 0 := by
  apply solutionCount_impossible
  intro assignment constraints
  obtain ⟨term, first, second⟩ := constraints (.equal left right) (by simp [pending])
  rcases missing with leftAbsent | rightAbsent
  · have absent := Symbolic.resolveContext_absent assignment left.fragment left.path leftAbsent
    rw [Symbolic.targetValue, absent] at first
    cases first
  · have absent := Symbolic.resolveContext_absent assignment right.fragment right.path rightAbsent
    rw [Symbolic.targetValue, absent] at second
    cases second

/-- Natural finite products agree with the source's unbounded integer multiplication. -/
theorem product_natCast (values : List Nat) : (values.map (fun value : Nat => (value : Int))).prod = (values.prod : Int) := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [List.map_cons, List.prod_cons, Int.natCast_mul, ih]

/-- A proved impossible problem makes the source's pure-zero result semantically correct. -/
theorem zero_result_correct (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (zero : solutionCount language problem = 0) (before after : Counts Symbol) (count : Int)
    (starts : SemanticCache language before) (success : (Except.ok (0, before) : Except Error _) = .ok (count, after)) :
    count = (solutionCount language problem : Int) ∧ SemanticCache language after := by
  cases success
  exact ⟨by rw [zero]; rfl, starts⟩

/-- Every actual pending-path solver branch preserves exact counts and both memo tables. -/
theorem solveStep_correct_step [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fallback : Term Symbol) (fuel : Nat) (nodeInduction : NodeCorrect graph meaning.terms fuel)
    (solveInduction : SolveCorrect graph meaning.terms fuel) (unifyInduction : UnifyCorrect graph meaning.terms fuel)
    (expandInduction : ExpandCorrect graph meaning.terms fuel) : StepCorrect graph meaning.terms (fuel + 1) := by
  intro problem before count after normal starts success
  cases pending : problem.obligations with
  | nil =>
      have verified := solveStep_independent graph (fun node => ((meaning.terms node).length : Int))
        (SemanticCache meaning.terms) fuel nodeInduction problem pending before after count starts success
      have independent := independent_solution_count meaning.terms fallback problem normal.1 normal.2.1 pending
      refine ⟨verified.1.trans ?_, verified.2⟩
      rw [independent]
      simpa only [List.map_map, Function.comp_def] using product_natCast (problem.domains.map fun entry => (meaning.terms entry.2).length)
  | cons first rest =>
      have tailNormal := normal_tail problem normal first rest pending
      have firstScope := normal.2.2.2 first (by simp [pending])
      cases first with
      | «exists» target =>
          have resolvedScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst)
            target.fragment target.path firstScope
          cases found : Symbolic.resolveContext target.fragment target.path with
          | absent =>
              simp only [solveStep, pending, found] at success
              exact zero_result_correct meaning.terms problem
                (absent_exists_count meaning.terms problem target rest pending found) before after count starts success
          | expand name =>
              simp only [solveStep, pending, found] at success
              simp only [found] at resolvedScope
              exact expandInduction problem name before count after normal resolvedScope starts success
          | resolved fragment =>
              simp only [solveStep, pending, found] at success
              have verified := solveInduction {problem with obligations := rest} before count after tailNormal.1
                (Or.inl tailNormal.2.1) starts success
              exact ⟨verified.1.trans (congrArg (fun size : Nat => (size : Int))
                (resolved_exists_count meaning.terms problem target rest fragment pending found).symm), verified.2⟩
      | equal left right =>
          have leftScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst)
            left.fragment left.path firstScope.1
          have rightScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst)
            right.fragment right.path firstScope.2
          cases leftFound : Symbolic.resolveContext left.fragment left.path with
          | absent =>
              simp only [solveStep, pending, leftFound] at success
              exact zero_result_correct meaning.terms problem
                (absent_equality_count meaning.terms problem left right rest pending (Or.inl leftFound)) before after count starts success
          | expand leftName =>
              simp only [leftFound] at leftScope
              cases rightFound : Symbolic.resolveContext right.fragment right.path with
              | absent =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  exact zero_result_correct meaning.terms problem
                    (absent_equality_count meaning.terms problem left right rest pending (Or.inr rightFound)) before after count starts success
              | expand rightName =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  exact expandInduction problem leftName before count after normal leftScope starts success
              | resolved second =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  exact expandInduction problem leftName before count after normal leftScope starts success
          | resolved first =>
              simp only [leftFound] at leftScope
              cases rightFound : Symbolic.resolveContext right.fragment right.path with
              | absent =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  exact zero_result_correct meaning.terms problem
                    (absent_equality_count meaning.terms problem left right rest pending (Or.inr rightFound)) before after count starts success
              | expand rightName =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  simp only [rightFound] at rightScope
                  exact expandInduction problem rightName before count after normal rightScope starts success
              | resolved second =>
                  simp only [solveStep, pending, leftFound, rightFound] at success
                  simp only [rightFound] at rightScope
                  have verified := unifyInduction {problem with obligations := rest} first second before count after tailNormal
                    leftScope rightScope starts success
                  exact ⟨verified.1.trans (congrArg (fun size : Nat => (size : Int))
                    (resolved_equality_count meaning.terms problem left right first second rest pending leftFound rightFound).symm), verified.2⟩

/-- All six actual mutually recursive functions preserve their independent finite-count semantics. -/
theorem counter_correct_mutual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fallback : Term Symbol) (fuel : Nat) :
    NodeCorrect graph meaning.terms fuel ∧ EdgeCorrect graph meaning.terms fuel ∧
      SolveCorrect graph meaning.terms fuel ∧ StepCorrect graph meaning.terms fuel ∧
      UnifyCorrect graph meaning.terms fuel ∧ ExpandCorrect graph meaning.terms fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ success; cases success
      · intro _ _ _ _ _ success; cases success
      · intro _ _ _ _ _ _ _ success; cases success
      · intro _ _ _ _ _ _ success; cases success
      · intro _ _ _ _ _ _ _ _ _ _ success; cases success
      · intro _ _ _ _ _ _ _ _ success; cases success
  | succ fuel ih =>
      obtain ⟨nodeInduction, edgeInduction, solveInduction, stepInduction, unifyInduction, expandInduction⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro node before count after starts success
        exact countNode_correct graph meaning fuel edgeInduction node before after count starts success
      · intro edge before count after starts success
        exact countEdge_correct graph meaning.terms (SemanticCache meaning.terms) fuel solveInduction edge before after count starts success
      · intro problem before count after distinct admissible starts success
        exact solve_correct graph meaning fuel stepInduction problem distinct admissible before after count starts success
      · exact solveStep_correct_step graph meaning fallback fuel nodeInduction solveInduction unifyInduction expandInduction
      · exact unify_correct_step graph meaning fuel solveInduction unifyInduction expandInduction
      · intro problem name before count after normal present starts success
        obtain ⟨entry, member, same⟩ := List.mem_map.mp present
        have selected : (name, entry.2) ∈ problem.domains := by simpa only [← same] using member
        exact expandVariable_correct graph meaning.terms meaning.distinct (SemanticCache meaning.terms) fuel solveInduction
          problem normal.1 normal.2.1 normal.2.2.2 normal.2.2.1 name entry.2 selected (meaning.indicators entry.2)
          before after count starts success

/-- The full source counter discharges the exact count contract used by the source decoder proofs. -/
theorem counter_countSound [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fallback : Term Symbol) : CountSound graph (fun node => (meaning.terms node).length) (SemanticCache meaning.terms) := by
  intro fuel
  exact (counter_correct_mutual graph meaning fallback fuel).1

/-- A successful public cardinality call returns exactly the number of distinct finite accepted terms. -/
theorem cardinality_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fallback : Term Symbol) (fuel root : Nat) (count : Int)
    (success : cardinality graph fuel root = .ok count) : count = ((meaning.terms root).length : Int) := by
  cases computed : countNode graph fuel root {} with
  | error error => simp only [cardinality, computed, Except.map] at success; cases success
  | ok pair =>
      obtain ⟨actual, after⟩ := pair
      simp only [cardinality, computed, Except.map, Except.ok.injEq] at success
      subst count
      exact ((counter_correct_mutual graph meaning fallback fuel).1 root {} actual after
        (semanticCache_empty meaning.terms) computed).1

end MicroCFTA.SymbolicDriver
