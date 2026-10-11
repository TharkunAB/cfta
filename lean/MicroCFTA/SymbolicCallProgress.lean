import MicroCFTA.SymbolicNormalizationTotal
import MicroCFTA.GraphBudget

/-!
# Structural progress of the actual symbolic call branches

The primary measure covers every structural edge, including rejected guard
components. The secondary measure counts pending context and path work.
The signed overlap map preserves structural bounds on all generated keys.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation Coefficients)

/-- Structural budgets on the source's identity-producing graph operations. -/
structure SourceBudget (graph : Graph Symbol) where
  value : Nat → Nat
  positive : ∀ node, 0 < value node
  edge : ∀ node alternative, alternative ∈ graph.edges node →
    (alternative.children.map value).sum < value node
  intersection : ∀ left right, value (graph.intersect left right) ≤ value left ∧ value (graph.intersect left right) ≤ value right

/-- Coefficient insertion preserves every property of the old keys and the inserted key. -/
theorem insertCoefficient_closed [DecidableEq Piece] (property : Piece → Prop) (entries : Coefficients Piece)
    (closed : ∀ entry ∈ entries, property entry.1) (key : Piece) (coefficient : Int) (valid : property key) :
    ∀ entry ∈ Symbolic.insertCoefficient key coefficient entries, property entry.1 := by
  intro entry member
  have keys := (Symbolic.insert_key_members key entry.1 coefficient entries).mp (List.mem_map.mpr ⟨entry, member, rfl⟩)
  rcases keys with same | old
  · simpa only [same] using valid
  · obtain ⟨original, originalMember, same⟩ := List.mem_map.mp old
    simpa only [same] using closed original originalMember

/-- Coefficient collection cannot introduce a new key outside a closed property. -/
theorem collect_closed [DecidableEq Piece] (property : Piece → Prop) (entries : Coefficients Piece)
    (closed : ∀ entry ∈ entries, property entry.1) : ∀ entry ∈ Symbolic.collect entries, property entry.1 := by
  induction entries with
  | nil => intro entry member; cases member
  | cons first rest ih =>
      apply insertCoefficient_closed property (Symbolic.collect rest)
        (ih (fun entry member => closed entry (by simp [member]))) first.1 first.2 (closed first (by simp))

/-- The actual signed union fold preserves every property closed under edge intersection. -/
theorem unionCoefficients_closed [DecidableEq Piece] (property : Piece → Prop)
    (meet : Piece → Piece → Option Piece)
    (intersection : ∀ left right common, property left → property right → meet left right = some common → property common)
    (keys : List Piece) (valid : ∀ key ∈ keys, property key) :
    ∀ entry ∈ Symbolic.unionCoefficients meet keys, property entry.1 := by
  have step : ∀ entries key, (∀ entry ∈ entries, property entry.1) → property key →
      ∀ entry ∈ Symbolic.addAlternative meet entries key, property entry.1 := by
    intro entries key old current entry member
    have retained := (List.mem_filter.mp member).1
    apply insertCoefficient_closed property _ ?_ key 1 current entry retained
    apply collect_closed
    intro component member
    rcases List.mem_append.mp member with previous | overlap
    · exact old component previous
    · obtain ⟨prior, priorMember, result⟩ := List.mem_filterMap.mp overlap
      cases found : meet key prior.1 with
      | none => simp only [found, Option.map_none] at result; cases result
      | some common =>
          simp only [found, Option.map_some, Option.some.injEq] at result
          subst component
          exact intersection key prior.1 common current (old prior priorMember) found
  have loop : ∀ (remaining : List Piece) (entries : Coefficients Piece), (∀ key ∈ remaining, property key) →
      (∀ entry ∈ entries, property entry.1) → ∀ entry ∈ remaining.foldl (Symbolic.addAlternative meet) entries, property entry.1 := by
    intro remaining
    induction remaining with
    | nil => intro entries _ old; exact old
    | cons key rest ih =>
        intro entries current old
        exact ih (Symbolic.addAlternative meet entries key) (fun other member => current other (by simp [member]))
          (step entries key old (current key (by simp)))
  exact loop keys [] valid (fun _ member => by cases member)

/-- Paired domain intersections cannot increase either complete child-tuple budget. -/
theorem intersect_children_budget (graph : Graph Symbol) (budget : SourceBudget graph) (left right : List Nat) :
    ((List.zipWith graph.intersect left right).map budget.value).sum ≤ (left.map budget.value).sum ∧
      ((List.zipWith graph.intersect left right).map budget.value).sum ≤ (right.map budget.value).sum := by
  induction left generalizing right with
  | nil => simp
  | cons first rest ih =>
      cases right with
      | nil => simp
      | cons second tail =>
          have childBound := budget.intersection first second
          have restBound := ih tail
          simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
          omega

/-- Actual source edge intersection retains both parent child-tuple bounds. -/
theorem intersectEdge_budget [DecidableEq Symbol] (graph : Graph Symbol) (budget : SourceBudget graph)
    (left right common : Edge Symbol) (success : intersectEdge graph left right = some common) :
    (common.children.map budget.value).sum ≤ (left.children.map budget.value).sum ∧
      (common.children.map budget.value).sum ≤ (right.children.map budget.value).sum := by
  unfold intersectEdge at success
  split at success
  · cases success
    exact intersect_children_budget graph budget left.children right.children
  · cases success

/-- Every generated overlap counted by a node has a strictly smaller complete child budget. -/
theorem union_edge_budget [DecidableEq Symbol] (graph : Graph Symbol) (budget : SourceBudget graph) (node : Nat)
    (entry : Edge Symbol × Int) (member : entry ∈ Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) :
    (entry.1.children.map budget.value).sum < budget.value node := by
  apply unionCoefficients_closed (fun edge => (edge.children.map budget.value).sum < budget.value node)
    (intersectEdge graph) ?_ (graph.edges node) (budget.edge node) entry member
  intro left right common leftBound _ found
  have smaller := (intersectEdge_budget graph budget left right common found).1
  omega

/-- Every pending requirement contributes positive work. -/
theorem obligationWork_positive (requirement : Obligation Symbol) : 0 < obligationWork (fun _ => 1) requirement := by
  cases requirement with
  | «exists» target =>
      have positive := fragmentWork_positive (fun _ => 1) (fun _ => Nat.zero_lt_one) target.fragment
      simp only [obligationWork, targetWork]
      omega
  | equal left right =>
      have positive := fragmentWork_positive (fun _ => 1) (fun _ => Nat.zero_lt_one) left.fragment
      simp only [obligationWork, targetWork]
      omega

/-- Removing a resolved head strictly decreases pending work. -/
theorem drop_obligation_progress (first : Obligation Symbol) (rest : List (Obligation Symbol)) :
    obligationsWork (fun _ => 1) rest < obligationsWork (fun _ => 1) (first :: rest) := by
  have positive := obligationWork_positive first
  simp only [obligationsWork, List.map_cons, List.sum_cons]
  omega

/-- Path resolution cannot enlarge a resolved context. -/
theorem resolved_context_work (fragment : Fragment Symbol) (path : List Nat) (resolved : Fragment Symbol)
    (found : Symbolic.resolveContext fragment path = .resolved resolved) :
    fragmentWork (fun _ => 1) resolved ≤ fragmentWork (fun _ => 1) fragment + path.length := by
  induction path generalizing fragment with
  | nil => cases found; omega
  | cons index rest ih =>
      cases fragment with
      | var name => cases found
      | constructor symbol children =>
          simp only [Symbolic.resolveContext] at found
          cases selected : children[index]? with
          | none => simp only [selected] at found; cases found
          | some child =>
              simp only [selected] at found
              have bounded := ih child found
              have parentBound := fragmentsWork_member (fun _ => 1) children child (List.mem_of_getElem? selected)
              simp only [fragmentWork, List.length_cons]
              omega

/-- The exact child-equation list has the sum of its two child-context work lists. -/
theorem child_equations_work (children others : List (Fragment Symbol)) (arity : children.length = others.length) :
    obligationsWork (fun _ => 1) (List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others) =
      fragmentsWork (fun _ => 1) children + fragmentsWork (fun _ => 1) others := by
  induction children generalizing others with
  | nil =>
      have empty : others = [] := List.length_eq_zero_iff.mp arity.symm
      subst others
      rfl
  | cons first rest ih =>
      cases others with
      | nil => simp at arity
      | cons second tail =>
          have tailArity : rest.length = tail.length := by simpa using arity
          have restWork := ih tail tailArity
          simp only [obligationsWork, List.zipWith_cons_cons, List.map_cons, List.sum_cons,
            obligationWork, targetWork, List.length_nil, Nat.add_zero, fragmentsWork] at restWork ⊢
          omega

/-- Comparing equal constructors strictly decreases pending work before normalization. -/
theorem constructor_children_progress (problem : Problem Symbol) (symbol : Symbol)
    (children others : List (Fragment Symbol)) (arity : children.length = others.length) :
    obligationsWork (fun _ => 1)
      (List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations) <
    obligationsWork (fun _ => 1) (equationProblem problem (.constructor symbol children) (.constructor symbol others)).obligations := by
  have childrenWork := child_equations_work children others arity
  simp only [obligationsWork, List.map_append, List.sum_append, equationProblem, List.map_cons, List.sum_cons,
    obligationWork, targetWork, List.length_nil, Nat.add_zero, fragmentWork] at childrenWork ⊢
  omega

end MicroCFTA.SymbolicDriver
