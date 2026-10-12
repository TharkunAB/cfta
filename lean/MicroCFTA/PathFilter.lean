import MicroCFTA.Template

/-!
# Constructor-preserving filters at selected child paths

The source uses `Needed` and `Edits` tries to require paths and to narrow nodes.
This module checks their graph action after sparse child keys are expanded to
ordered child plans. An empty child plan is the identity. A terminal plan
intersects the selected node with a term predicate.
-/

namespace MicroCFTA.PathFilter
open Language

/-- A terminal intersection or an ordered prefix of child edits. -/
inductive Plan (Symbol : Type) where
  | here (predicate : Term Symbol → Bool)
  | branches (children : List (Plan Symbol))

/-- An empty edit trie leaves every constructor and child unchanged. -/
def identity : Plan Symbol := .branches []

/-- A terminal edit checks its selected complete subtree. -/
def rootTest : Plan Symbol → Term Symbol → Bool
  | .here predicate, term => predicate term
  | .branches _, _ => true

/-- Requiring paths checks the greatest child key; editing alone ignores absent children. -/
def childPlans (require : Bool) (plan : Plan Symbol) (arity : Nat) : Option (List (Plan Symbol)) :=
  match plan with
  | .here _ => some (List.replicate arity identity)
  | .branches children =>
    if require = true ∧ arity < children.length then none
    else some (children.take arity ++ List.replicate (arity - children.length) identity)

/-- Every successful alignment keeps exactly the source child count. -/
theorem childPlans_length (require : Bool) (plan : Plan Symbol) (arity : Nat) (plans : List (Plan Symbol))
    (aligned : childPlans require plan arity = some plans) : plans.length = arity := by
  cases plan with
  | here predicate => simp [childPlans] at aligned; subst plans; simp
  | branches children =>
    simp only [childPlans] at aligned
    split at aligned
    · cases aligned
    · cases aligned
      simp only [List.length_append, List.length_take, List.length_replicate]
      omega

/-- Independent complete-term semantics of the finite edit trie. -/
inductive Matches (require : Bool) : Plan Symbol → Term Symbol → Prop where
  | node (plan : Plan Symbol) (symbol : Symbol) (terms : List (Term Symbol)) (plans : List (Plan Symbol)) :
      childPlans require plan terms.length = some plans → All₂ (Matches require) plans terms →
      rootTest plan (.node symbol terms) = true → Matches require plan (.node symbol terms)

/-- The empty plan admits every complete term. -/
theorem identity_matches (require : Bool) (term : Term Symbol) : Matches require identity term := by
  induction term using Term.rec
    (motive_2 := fun terms => All₂ (Matches require) (List.replicate terms.length identity) terms) with
  | node symbol terms ih => exact .node identity symbol terms _ (by simp [childPlans, identity]) ih rfl
  | nil => exact .nil
  | cons term rest first tail => exact .cons first tail

/-- A terminal edit denotes exactly its complete-subtree predicate. -/
theorem here_exact (require : Bool) (predicate : Term Symbol → Bool) (term : Term Symbol) :
    Matches require (.here predicate) term ↔ predicate term = true := by
  cases term with
  | node symbol terms =>
    constructor
    · intro accepted; cases accepted with | node _ _ _ _ _ _ guard => exact guard
    · intro guard
      have children : ∀ values : List (Term Symbol), All₂ (Matches require) (List.replicate values.length identity) values := by
        intro values
        induction values with
        | nil => exact .nil
        | cons value values ih => exact .cons (identity_matches require value) ih
      exact .node (.here predicate) symbol terms _ rfl (children terms) guard

/-- Copy an original edge and apply the aligned child edits and terminal test. -/
def restrictEdge (require : Bool) (plan : Plan Symbol) (edge : Edge State Symbol) :
    List (Edge (State × Plan Symbol) Symbol) :=
  match childPlans require plan edge.children.length with
  | none => []
  | some plans => [⟨edge.label, edge.children.zip plans, fun term => edge.guard term && rootTest plan term⟩]

/-- The graph action copies each source constructor with its complete original guard. -/
def restrict (require : Bool) (graph : Automaton State Symbol) : Automaton (State × Plan Symbol) Symbol :=
  fun (state, plan) => (graph state).flatMap (restrictEdge require plan)

/-- Every output row is one original row with the exact aligned edits. -/
theorem row_exact (require : Bool) (graph : Automaton State Symbol) (state : State)
    (plan : Plan Symbol) (edge : Edge (State × Plan Symbol) Symbol) :
    edge ∈ restrict require graph (state, plan) ↔
      ∃ original ∈ graph state, ∃ plans,
        childPlans require plan original.children.length = some plans ∧
        edge = ⟨original.label, original.children.zip plans, fun term => original.guard term && rootTest plan term⟩ := by
  simp only [restrict, List.mem_flatMap]
  constructor
  · rintro ⟨original, present, member⟩
    unfold restrictEdge at member
    cases aligned : childPlans require plan original.children.length with
    | none => simp [aligned] at member
    | some plans => exact ⟨original, present, plans, aligned, by simpa [aligned] using member⟩
  · rintro ⟨original, present, plans, aligned, rfl⟩
    exact ⟨original, present, by simp [restrictEdge, aligned]⟩

/-- A copied graph run is an original run that satisfies every selected edit. -/
theorem restrict_sound (require : Bool) (graph : Automaton State Symbol)
    {pair : State × Plan Symbol} {term : Term Symbol}
    (accepted : Accepts (restrict require graph) pair term) :
    Accepts graph pair.1 term ∧ Matches require pair.2 term := by
  induction accepted using Accepts.rec
    (motive_2 := fun pairs terms _ => All₂ (fun (pair : State × Plan Symbol) term =>
      Accepts graph pair.1 term ∧ Matches require pair.2 term) pairs terms) with
  | @node pair edge terms present children guard ih =>
    obtain ⟨original, member, plans, aligned, rfl⟩ := (row_exact require graph pair.1 pair.2 edge).mp present
    have parts := (all₂_zip_iff (Accepts graph) (Matches require) _ _ _
      (childPlans_length require pair.2 original.children.length plans aligned).symm).mp ih
    have tests : original.guard (.node original.label terms) = true ∧ rootTest pair.2 (.node original.label terms) = true := by simpa only [Bool.and_eq_true] using guard
    exact ⟨.node original terms member parts.1 tests.1,
      .node pair.2 original.label terms plans (by simpa [← parts.1.length_eq] using aligned) parts.2 tests.2⟩
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Every original term that satisfies the edit trie has a copied accepting run. -/
theorem restrict_complete (require : Bool) (graph : Automaton State Symbol) {state term}
    (accepted : Accepts graph state term) :
    ∀ plan, Matches require plan term → Accepts (restrict require graph) (state, plan) term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => ∀ plans, All₂ (Matches require) plans terms →
      All₂ (Accepts (restrict require graph)) (states.zip plans) terms) with
  | @node state original terms member runs guard ih =>
    intro plan matched
    cases matched with
    | node _ _ _ plans aligned children rootGuard =>
      have alignment : childPlans require plan original.children.length = some plans := by
        simpa [runs.length_eq] using aligned
      exact .node _ terms ((row_exact require graph state plan _).mpr ⟨original, member, plans, alignment, rfl⟩)
        (ih plans children) (by simpa only [Bool.and_eq_true] using And.intro guard rootGuard)
  | nil plans matched => cases matched; exact .nil
  | cons _ _ head tail plans matched =>
    cases matched with
    | cons first rest => exact .cons (head _ first) (tail _ rest)

/-- Batched constructor-path filtering preserves exactly the required original terms. -/
theorem restrict_exact (require : Bool) (graph : Automaton State Symbol)
    (state : State) (plan : Plan Symbol) (term : Term Symbol) :
    Accepts (restrict require graph) (state, plan) term ↔ Accepts graph state term ∧ Matches require plan term :=
  ⟨restrict_sound require graph, fun ⟨accepted, matched⟩ => restrict_complete require graph accepted plan matched⟩

/-- A known child alignment exposes exactly the child conditions and root test. -/
theorem matches_aligned (require : Bool) (plan : Plan Symbol) (symbol : Symbol)
    (terms : List (Term Symbol)) (plans : List (Plan Symbol))
    (aligned : childPlans require plan terms.length = some plans) :
    Matches require plan (.node symbol terms) ↔
      All₂ (Matches require) plans terms ∧ rootTest plan (.node symbol terms) = true := by
  constructor
  · intro accepted
    cases accepted with
    | node _ _ _ actual actualAligned children guard =>
      have same := Option.some.inj (actualAligned.symm.trans aligned)
      subst actual
      exact ⟨children, guard⟩
  · rintro ⟨children, guard⟩; exact .node plan symbol terms plans aligned children guard

/-- A rejected child alignment admits no term. -/
theorem matches_rejected (require : Bool) (plan : Plan Symbol) (symbol : Symbol)
    (terms : List (Term Symbol)) (rejected : childPlans require plan terms.length = none) :
    ¬ Matches require plan (.node symbol terms) := by
  intro accepted
  cases accepted with
  | node _ _ _ plans aligned => rw [rejected] at aligned; cases aligned

/-- Identity plans preserve the complete ordered child forest. -/
theorem identity_forest (require : Bool) (terms : List (Term Symbol)) :
    All₂ (Matches require) (List.replicate terms.length identity) terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (identity_matches require term) ih

/-- One selected child leaves every other child unrestricted. -/
theorem indexed_matches (require : Bool) (index : Nat) (plan : Plan Symbol)
    (terms : List (Term Symbol)) (inside : index < terms.length) :
    All₂ (Matches require) (List.replicate index identity ++ plan ::
      List.replicate (terms.length - index - 1) identity) terms ↔ Matches require plan terms[index] := by
  induction index generalizing terms with
  | zero =>
    cases terms with
    | nil => simp at inside
    | cons term terms =>
      simp only [List.replicate_zero, List.nil_append, List.length_cons, Nat.sub_zero, Nat.add_sub_cancel,
        List.getElem_cons_zero]
      constructor
      · intro related; cases related with | cons head _ => exact head
      · intro head; exact .cons head (identity_forest require terms)
  | succ index ih =>
    cases terms with
    | nil => simp at inside
    | cons term terms =>
      have bound : index < terms.length := by simpa using inside
      have size : (term :: terms).length - (index + 1) - 1 = terms.length - index - 1 := by simp
      simp only [List.replicate_succ, List.cons_append, size, List.getElem_cons_succ]
      constructor
      · intro related; cases related with | cons _ tail => exact (ih terms bound).mp tail
      · intro selected; exact .cons (identity_matches require term) ((ih terms bound).mpr selected)

/-- Insert one terminal edit at a complete path. -/
def pathPlan (predicate : Term Symbol → Bool) : List Nat → Plan Symbol
  | [] => .here predicate
  | index :: rest => .branches (List.replicate index identity ++ [pathPlan predicate rest])

/-- At an existing child, the ordered edit prefix has the exact selected alignment. -/
theorem at_childPlans (require : Bool) (predicate : Term Symbol → Bool) (index : Nat) (rest : List Nat)
    (arity : Nat) (inside : index < arity) :
    childPlans require (pathPlan predicate (index :: rest)) arity =
      some (List.replicate index identity ++ pathPlan predicate rest :: List.replicate (arity - index - 1) identity) := by
  have length : (List.replicate index (identity : Plan Symbol) ++ [pathPlan predicate rest]).length = index + 1 := by simp
  have enough : (List.replicate index (identity : Plan Symbol) ++ [pathPlan predicate rest]).length ≤ arity := by omega
  have no : ¬arity < index + 1 := by omega
  simp [pathPlan, childPlans, length, no, List.take_of_length_le enough, List.append_assoc,
    show arity - (index + 1) = arity - index - 1 by omega]

/-- An absent selected child is rejected when the path is required. -/
theorem at_child_missing (predicate : Term Symbol → Bool) (index : Nat) (rest : List Nat)
    (arity : Nat) (outside : arity ≤ index) :
    childPlans true (pathPlan predicate (index :: rest)) arity = none := by
  simp [pathPlan, childPlans, show arity < index + 1 by omega]

/-- An edit with no selected child leaves the existing child list unchanged. -/
theorem at_child_absent (predicate : Term Symbol → Bool) (index : Nat) (rest : List Nat)
    (arity : Nat) (outside : arity ≤ index) :
    childPlans false (pathPlan predicate (index :: rest)) arity = some (List.replicate arity identity) := by
  simp [pathPlan, childPlans, List.take_append_of_le_length (by simpa using outside : arity ≤ (List.replicate index (identity : Plan Symbol)).length),
    Nat.min_eq_left outside, show arity - (index + 1) = 0 by omega]

/-- The graph path edit has the exact existing-subtree test, including absent-path behavior. -/
theorem at_exact (require : Bool) (predicate : Term Symbol → Bool) (path : List Nat) (term : Term Symbol) :
    Matches require (pathPlan predicate path) term ↔
      match term.atPath path with
      | none => require = false
      | some subtree => predicate subtree = true := by
  induction path generalizing term with
  | nil => simpa only [pathPlan, Term.atPath] using here_exact require predicate term
  | cons index rest ih =>
    cases term with
    | node symbol terms =>
      by_cases inside : index < terms.length
      · rw [matches_aligned require _ symbol terms _ (at_childPlans require predicate index rest terms.length inside)]
        simp only [pathPlan, rootTest, and_true, indexed_matches require index _ terms inside]
        simpa only [Term.atPath, List.getElem?_eq_getElem inside, Option.bind_some] using ih terms[index]
      · have outside : terms.length ≤ index := by omega
        simp only [Term.atPath, List.getElem?_eq_none outside, Option.bind_none]
        cases require with
        | true =>
          have rejected := matches_rejected true _ symbol terms (at_child_missing predicate index rest terms.length outside)
          simp [rejected]
        | false =>
          rw [matches_aligned false _ symbol terms _ (at_child_absent predicate index rest terms.length outside)]
          simp only [pathPlan, rootTest, and_true, identity_forest, iff_self]

/-- Requiring and intersecting a path keeps all and only its matching original terms. -/
theorem require_exact (graph : Automaton State Symbol) (state : State) (path : List Nat)
    (predicate : Term Symbol → Bool) (term : Term Symbol) :
    Accepts (restrict true graph) (state, pathPlan predicate path) term ↔
      Accepts graph state term ∧ ∃ subtree, term.atPath path = some subtree ∧ predicate subtree = true := by
  rw [restrict_exact, at_exact]
  cases found : term.atPath path <;> simp

end MicroCFTA.PathFilter
