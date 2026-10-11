import MicroCFTA.SymbolicBranchTotal

/-!
# Complete counter termination at a sufficient execution bound

The proof uses the well-founded source call relation. Every recursive call
retains the variable scope required by normalization. Finite state traversals
combine stable child bounds and preserve their exact memo-table outputs.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation)

/-- The caller invariants needed for successful source execution. -/
def CounterCallValid : CounterCall Symbol → Prop
  | .node _ | .edge _ => True
  | .solve problem weight => BindingBudget weight problem.bindings ∧ InputScope problem
  | .step problem => NormalProblem problem
  | .unify problem left right => NormalProblem problem ∧
      InScope (fun name => name ∈ problem.domains.map Prod.fst) left ∧
      InScope (fun name => name ∈ problem.domains.map Prod.fst) right
  | .expand problem name => NormalProblem problem ∧ name ∈ problem.domains.map Prod.fst

/-- Interpret one control location with the actual bounded source function. -/
def counterCallAction [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (call : CounterCall Symbol)
    (fuel : Nat) : CountM Symbol Int :=
  match call with
  | .node node => countNode graph fuel node
  | .edge edge => countEdge graph fuel edge
  | .solve problem _ => solve graph fuel problem
  | .step problem => solveStep graph fuel problem
  | .unify problem left right => unify graph fuel problem left right
  | .expand problem name => expandVariable graph fuel problem name

/-- Normalized problems satisfy the complete raw solve-call invariant with unit variable weights. -/
theorem normal_solve_valid (problem : Problem Symbol) (normal : NormalProblem problem) :
    CounterCallValid (.solve problem (fun _ => 1)) :=
  ⟨empty_binding_budget problem normal.2.1, normal_inputScope problem normal⟩

/-- Every valid actual source counter call returns the same successful result and cache at all sufficiently large bounds. -/
theorem counter_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (budget : SourceBudget graph)
    (call : CounterCall Symbol) : CounterCallValid call → ∀ initial, Eventually (counterCallAction graph call) initial := by
  apply (counter_calls_wellFounded graph budget).induction call
  intro current ih valid initial
  cases current with
  | node node =>
      apply countNode_eventual graph node
      intro piece member state
      exact ih (.edge piece.1) (.nodeEdge node piece member) trivial state
  | edge edge =>
      apply countEdge_eventual graph edge
      intro piece member state
      exact ih (.solve (edgeProblem edge piece.2) (fun _ => 1)) (.edgeSolve edge piece member)
        (normal_solve_valid _ (edgeProblem_normal edge piece.2)) state
  | solve problem weight =>
      apply solve_eventual graph problem weight valid.1 valid.2
      intro normalized fuel success state
      exact ih (.step normalized) (.solveStep problem normalized weight fuel valid.1 success)
        (normalize_normal fuel problem normalized success) state
  | step problem =>
      cases pending : problem.obligations with
      | nil =>
          apply eventually_succ (counterCallAction graph (.step problem))
            (fun fuel => do let counts ← problem.domains.mapM fun entry => countNode graph fuel entry.2; pure counts.prod) initial
          · intro fuel; simp only [counterCallAction, solveStep, pending]
          · apply eventually_bind _ _ initial
            · apply eventually_mapM
              intro entry member state
              exact ih (.node entry.2) (.stepDomain problem entry member) trivial state
            · intro values state; exact eventually_pure values.prod state
      | cons first rest =>
          have tailNormal := normal_tail problem valid first rest pending
          have headScope := valid.2.2.2 first (by simp [pending])
          cases first with
          | «exists» target =>
              have resolvedScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst)
                target.fragment target.path headScope
              cases found : Symbolic.resolveContext target.fragment target.path with
              | absent =>
                  apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                  intro fuel; simp only [counterCallAction, solveStep, pending, found]
              | expand name =>
                  simp only [found] at resolvedScope
                  apply eventually_succ _ (counterCallAction graph (.expand problem name)) initial ?_
                    (ih _ (.stepExpand problem name) ⟨valid, resolvedScope⟩ initial)
                  intro fuel; simp only [counterCallAction, solveStep, pending, found]
              | resolved fragment =>
                  apply eventually_succ _ (counterCallAction graph (.solve {problem with obligations := rest} (fun _ => 1))) initial ?_
                    (ih _ (.stepExists problem target rest pending) (normal_solve_valid _ tailNormal) initial)
                  intro fuel; simp only [counterCallAction, solveStep, pending, found]
          | equal left right =>
              have leftScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst) left.fragment left.path headScope.1
              have rightScope := resolveContext_scope (fun name => name ∈ problem.domains.map Prod.fst) right.fragment right.path headScope.2
              cases leftFound : Symbolic.resolveContext left.fragment left.path with
              | absent =>
                  apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                  intro fuel; simp only [counterCallAction, solveStep, pending, leftFound]
              | expand leftName =>
                  simp only [leftFound] at leftScope
                  cases rightFound : Symbolic.resolveContext right.fragment right.path with
                  | absent =>
                      apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
                  | expand rightName =>
                      apply eventually_succ _ (counterCallAction graph (.expand problem leftName)) initial ?_
                        (ih _ (.stepExpand problem leftName) ⟨valid, leftScope⟩ initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
                  | resolved second =>
                      apply eventually_succ _ (counterCallAction graph (.expand problem leftName)) initial ?_
                        (ih _ (.stepExpand problem leftName) ⟨valid, leftScope⟩ initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
              | resolved first =>
                  simp only [leftFound] at leftScope
                  cases rightFound : Symbolic.resolveContext right.fragment right.path with
                  | absent =>
                      apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
                  | expand rightName =>
                      simp only [rightFound] at rightScope
                      apply eventually_succ _ (counterCallAction graph (.expand problem rightName)) initial ?_
                        (ih _ (.stepExpand problem rightName) ⟨valid, rightScope⟩ initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
                  | resolved second =>
                      simp only [rightFound] at rightScope
                      apply eventually_succ _ (counterCallAction graph (.unify {problem with obligations := rest} first second)) initial ?_
                        (ih _ (.stepUnify problem left right first second rest pending leftFound rightFound) ⟨tailNormal, leftScope, rightScope⟩ initial)
                      intro fuel; simp only [counterCallAction, solveStep, pending, leftFound, rightFound]
  | unify problem left right =>
      obtain ⟨normal, leftScope, rightScope⟩ := valid
      cases left with
      | var left =>
          cases right with
          | var right =>
              by_cases same : left = right
              · subst right
                apply eventually_succ _ (counterCallAction graph (.solve problem (fun _ => 1))) initial ?_
                  (ih _ (.unifySame problem left) (normal_solve_valid problem normal) initial)
                intro fuel; simp only [counterCallAction, unify, ite_true]
              · obtain ⟨leftNode, leftMember⟩ := scoped_variable_domain problem left leftScope
                obtain ⟨rightNode, rightMember⟩ := scoped_variable_domain problem right rightScope
                let merged := mergedProblem problem left right (graph.intersect leftNode rightNode)
                have admissible := mergedProblem_admissible problem normal.1 normal.2.1 left right (graph.intersect leftNode rightNode) same
                obtain ⟨weight, bindingBudget⟩ := admissible_binding_budget merged admissible.2
                have recursive := ih (.solve merged weight)
                  (.unifyMerge problem left right leftNode rightNode weight normal.1 same leftMember rightMember)
                  ⟨bindingBudget, mergedProblem_inputScope problem normal left right (graph.intersect leftNode rightNode)⟩ initial
                have leftFound : domain problem left = .ok leftNode := by
                  simp only [domain, lookup_of_member problem.domains normal.1 left leftNode leftMember]
                have rightFound : domain problem right = .ok rightNode := by
                  simp only [domain, lookup_of_member problem.domains normal.1 right rightNode rightMember]
                apply eventually_succ _ (counterCallAction graph (.solve merged weight)) initial ?_ recursive
                intro fuel
                simp only [counterCallAction, unify, ite_eq_right same, leftFound, rightFound, Bind.bind,
                  liftM, monadLift, MonadLift.monadLift, merged, mergedProblem]
                rfl
          | constructor symbol children =>
              by_cases occurrence : occurs left (.constructor symbol children) = true
              · apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                intro fuel; simp only [counterCallAction, unify, occurrence, ite_true]
              · have notOccurs : occurs left (.constructor symbol children) = false := Bool.eq_false_iff.mpr occurrence
                have nextNormal := normal_equation problem normal (.var left) (.constructor symbol children) leftScope rightScope
                apply eventually_succ _ (counterCallAction graph (.expand (equationProblem problem (.var left) (.constructor symbol children)) left)) initial ?_
                  (ih _ (.unifyExpand problem left symbol children) ⟨nextNormal, leftScope left (by simp [occurs])⟩ initial)
                intro fuel; simp only [counterCallAction, unify, notOccurs, Bool.false_eq_true, ite_false, equationProblem]
      | constructor symbol children =>
          cases right with
          | var right =>
              apply eventually_succ _ (counterCallAction graph (.unify problem (.var right) (.constructor symbol children))) initial ?_
                (ih _ (.unifySwap problem right symbol children) ⟨normal, rightScope, leftScope⟩ initial)
              intro fuel; rfl
          | constructor other others =>
              by_cases different : symbol ≠ other ∨ children.length ≠ others.length
              · apply eventually_succ _ (fun _ => pure 0) initial ?_ (eventually_pure 0 initial)
                intro fuel; simp only [counterCallAction, unify, ite_eq_left different]
              · have same : symbol = other := Classical.byContradiction (fun unequal => different (Or.inl unequal))
                have arity : children.length = others.length := Classical.byContradiction (fun unequal => different (Or.inr unequal))
                subst other
                let nextProblem := {problem with
                  obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations}
                have nextNormal := normal_children problem normal symbol children others leftScope rightScope
                apply eventually_succ _ (counterCallAction graph (.solve nextProblem (fun _ => 1))) initial ?_
                  (ih _ (.unifyChildren problem symbol children others arity) (normal_solve_valid nextProblem nextNormal) initial)
                intro fuel; simp only [counterCallAction, unify, ite_eq_right different, nextProblem]
  | expand problem name =>
      obtain ⟨normal, present⟩ := valid
      obtain ⟨entry, member, same⟩ := List.mem_map.mp present
      have selected : (name, entry.2) ∈ problem.domains := by simpa only [← same] using member
      have found : domain problem name = .ok entry.2 := by
        simp only [domain, lookup_of_member problem.domains normal.1 name entry.2 selected]
      let action := fun fuel (edge : Edge Symbol) => (do
        let values ← edge.indicators.mapM fun (coefficient, classes) => do
          let count ← solve graph fuel (expandedProblem problem name edge classes)
          pure (coefficient * count)
        pure values.sum : CountM Symbol Int)
      have total : Eventually (fun fuel => countUnion graph (action fuel) (graph.edges entry.2)) initial := by
        apply countUnion_eventually
        intro piece pieceMember state
        apply eventually_bind _ _ state
        · apply eventually_mapM
          intro component _ cache
          have admissible := expandedProblem_admissible problem normal.1 normal.2.1 normal.2.2.1 name entry.2 selected piece.1 component.2
          obtain ⟨weight, bindingBudget⟩ := admissible_binding_budget (expandedProblem problem name piece.1 component.2) admissible.2
          have recursive := ih (.solve (expandedProblem problem name piece.1 component.2) weight)
            (.expandSolve problem name entry.2 piece component.2 weight normal.1 selected pieceMember)
            ⟨bindingBudget, expandedProblem_inputScope problem normal name piece.1 component.2⟩ cache
          exact eventually_bind _ _ cache recursive (fun count finalState => eventually_pure (component.1 * count) finalState)
        · intro values cache; exact eventually_pure values.sum cache
      apply eventually_succ _ (fun fuel => countUnion graph (action fuel) (graph.edges entry.2)) initial ?_ total
      intro fuel
      funext cache
      simp only [counterCallAction, expandVariable, found, action, expandedProblem, expansionContext, Bind.bind, StateT.bind,
        liftM, monadLift, MonadLift.monadLift, StateT.lift, Pure.pure, Except.pure, Except.bind]

/-- Every finite structurally acyclic source graph has one stable successful cardinality bound. -/
theorem cardinality_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (budget : SourceBudget graph) (root : Nat) :
    ∃ bound count, ∀ fuel, bound ≤ fuel → cardinality graph fuel root = .ok count := by
  obtain ⟨bound, count, cache, stable⟩ := counter_eventual graph budget (.node root) trivial {}
  refine ⟨bound, count, ?_⟩
  intro fuel enough
  simp only [counterCallAction] at stable
  simp only [cardinality, stable fuel enough, Except.map]

/-- At every sufficiently large bound, public cardinality returns the exact distinct finite language size. -/
theorem cardinality_total_exact [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (budget : SourceBudget graph) (meaning : CounterMeaning graph) (fallback : Term Symbol) (root : Nat) :
    ∃ bound, ∀ fuel, bound ≤ fuel → cardinality graph fuel root = .ok ((meaning.terms root).length : Int) := by
  obtain ⟨bound, count, stable⟩ := cardinality_eventual graph budget root
  have correct := cardinality_correct graph meaning fallback bound root count (stable bound (Nat.le_refl _))
  subst count
  exact ⟨bound, stable⟩

end MicroCFTA.SymbolicDriver
