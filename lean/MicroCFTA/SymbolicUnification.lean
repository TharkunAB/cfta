import MicroCFTA.SymbolicCounterCache

/-!
# Source unification semantics and caller invariants

Whole-context equations are kept separate from the remaining problem.
Constructor comparison, occurs rejection, and variable merging preserve
the same finite live-tuple semantics used by the counter.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation instantiate instantiateMany Satisfies)

/-- Reintroduce the whole-context equality passed separately to `unify`. -/
def equationProblem (problem : Problem Symbol) (left right : Fragment Symbol) : Problem Symbol :=
  {problem with obligations := .equal ⟨left, []⟩ ⟨right, []⟩ :: problem.obligations}

/-- Equality between two complete contexts compares exactly their instantiated terms. -/
theorem whole_equation_iff (assignment : Nat → Term Symbol) (left right : Fragment Symbol) :
    Satisfies assignment (.equal ⟨left, []⟩ ⟨right, []⟩) ↔ instantiate assignment left = instantiate assignment right := by
  simp only [Satisfies, Symbolic.targetValue, Term.atPath]
  constructor
  · rintro ⟨term, first, second⟩
    exact Option.some.inj (first.trans second.symm)
  · intro same
    exact ⟨instantiate assignment right, congrArg some same, rfl⟩

/-- Removing a whole-context self equation preserves exact finite counts. -/
theorem equation_reflexive_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol) (fragment : Fragment Symbol) :
    solutionCount language (equationProblem problem fragment fragment) = solutionCount language problem := by
  have equal := solutionCount_obligations language (equationProblem problem fragment fragment) problem.obligations (by
    intro assignment
    simp only [equationProblem, List.forall_mem_cons, whole_equation_iff, true_and])
  exact equal

/-- Swapping the two equation contexts does not change the finite count. -/
theorem equation_symmetric_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol) (left right : Fragment Symbol) :
    solutionCount language (equationProblem problem left right) = solutionCount language (equationProblem problem right left) := by
  apply solutionCount_obligations
  intro assignment
  simp only [equationProblem, List.forall_mem_cons, whole_equation_iff, eq_comm]

/-- Context instantiation preserves the number of ordered constructor children. -/
theorem instantiateMany_length (assignment : Nat → Term Symbol) (children : List (Fragment Symbol)) :
    (instantiateMany assignment children).length = children.length := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [instantiateMany, List.length_cons, ih]

/-- Different constructor tags or arities cannot satisfy a whole-context equation. -/
theorem constructor_mismatch_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (left right : Symbol) (children others : List (Fragment Symbol))
    (different : left ≠ right ∨ children.length ≠ others.length) :
    solutionCount language (equationProblem problem (.constructor left children) (.constructor right others)) = 0 := by
  apply solutionCount_impossible
  intro assignment constraints
  have equal := (whole_equation_iff assignment (.constructor left children) (.constructor right others)).mp
    (constraints (.equal ⟨.constructor left children, []⟩ ⟨.constructor right others, []⟩) (by simp [equationProblem]))
  have same := Term.node.inj equal
  rcases different with symbolDifferent | arityDifferent
  · exact symbolDifferent same.1
  · apply arityDifferent
    simpa only [instantiateMany_length] using congrArg List.length same.2

/-- Equal constructors reduce to the exact source list of pairwise child equations. -/
theorem constructor_children_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (symbol : Symbol) (children others : List (Fragment Symbol)) (arity : children.length = others.length) :
    solutionCount language (equationProblem problem (.constructor symbol children) (.constructor symbol others)) =
      solutionCount language {problem with
        obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations} := by
  apply solutionCount_obligations
  intro assignment
  simp only [equationProblem, List.forall_mem_cons, List.forall_mem_append, whole_equation_iff,
    constructor_obligations_semantics assignment symbol children others arity]

/-- Distinct whole-variable merging preserves the source's admissible substitution shape. -/
theorem mergedProblem_admissible (problem : Problem Symbol) (distinct : (problem.domains.map Prod.fst).Nodup)
    (empty : problem.bindings = []) (left right common : Nat) (different : left ≠ right) :
    ((mergedProblem problem left right common).domains.map Prod.fst).Nodup ∧
      AdmissibleBindings (mergedProblem problem left right common) := by
  refine ⟨insert_distinct _ (delete_distinct _ distinct left) right common, Or.inr ?_⟩
  refine ⟨left, .var right, ?_, ?_, ?_⟩
  · simp [mergedProblem, empty, insert, delete]
  · intro present
    obtain ⟨entry, member, same⟩ := List.mem_map.mp present
    rcases (insert_member (delete problem.domains left) right common entry).mp member with rfl | old
    · exact different same.symm
    · have retained := (List.mem_filter.mp old.1).2
      simp only [same, bne_self_eq_false, Bool.false_eq_true] at retained
  · exact beq_eq_false_iff_ne.mpr different

/-- A scoped constructor gives the same variable scope to every child context. -/
theorem constructor_child_scope (allowed : Nat → Prop) (symbol : Symbol) (children : List (Fragment Symbol))
    (within : InScope allowed (.constructor symbol children)) :
    ∀ child ∈ children, InScope allowed child := by
  intro child member name occursChild
  apply within name
  change occursMany name children = true
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [occursMany, occursChild]
      · simp only [occursMany, Bool.or_eq_true]
        exact Or.inr (ih (fun key occurrence => within key (by
          change occursMany key rest = true at occurrence
          simp [occurs, occursMany, occurrence])) member)

/-- Resolving a scoped path keeps a resolved context scoped and expands only a live variable. -/
theorem resolveContext_scope (allowed : Nat → Prop) (fragment : Fragment Symbol) (path : List Nat)
    (within : InScope allowed fragment) :
    match Symbolic.resolveContext fragment path with
    | .absent => True
    | .resolved context => InScope allowed context
    | .expand name => allowed name := by
  induction path generalizing fragment with
  | nil => simpa only [Symbolic.resolveContext] using within
  | cons index rest ih =>
      cases fragment with
      | var name => exact within name (by simp [occurs])
      | constructor symbol children =>
          simp only [Symbolic.resolveContext]
          cases found : children[index]? with
          | none => trivial
          | some child =>
              exact ih child (constructor_child_scope allowed symbol children within child (List.mem_of_getElem? found))

/-- A new scoped whole equation preserves the normalized problem's shape and live scope. -/
theorem normal_equation (problem : Problem Symbol) (normal : NormalProblem problem) (left right : Fragment Symbol)
    (leftScope : InScope (fun name => name ∈ problem.domains.map Prod.fst) left)
    (rightScope : InScope (fun name => name ∈ problem.domains.map Prod.fst) right) :
    NormalProblem (equationProblem problem left right) := by
  refine ⟨normal.1, normal.2.1, normal.2.2.1, ?_⟩
  intro obligation member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨leftScope, rightScope⟩
  · exact normal.2.2.2 obligation member

end MicroCFTA.SymbolicDriver
