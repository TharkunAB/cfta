import MicroCFTA.PruneSchedule
import MicroCFTA.Binding

/-!
# The recursion-read gate on stored binder shapes

The repaired source inspects an open binder's stored body before asking for
its outer alternatives. It never unfolds the binder in this check. Every
recursive call descends a finite stored shape, a member list, or a child list.
-/
namespace MicroCFTA.PruneReads
open Binding Observation PruneSchedule

mutual
  /-- Detect a reference along a planned read without unfolding an open binder. -/
  def reaches (plan : Plan) : Shape Payload → Bool
    | .empty => false
    | .ref _ => true
    | .alternatives members => reachesMembers plan members
    | node@(.binder _ body) => !(free node).isEmpty && reaches plan body
    | node@(.branch _ children) =>
        !(free node).isEmpty && match plan with
          | .node _ planned => reachesChildren planned 0 children

  /-- A union reaches recursion if any stored member does. -/
  def reachesMembers (plan : Plan) : List (Shape Payload) → Bool
    | [] => false
    | first :: rest => reaches plan first || reachesMembers plan rest

  /-- Inspect existing child positions requested by the sparse plan. -/
  def reachesChildren (planned : List (Nat × Plan)) (index : Nat) : List (Shape Payload) → Bool
    | [] => false
    | child :: rest =>
        (match childAt index planned with
         | none => false
         | some plan => reaches plan child) || reachesChildren planned (index + 1) rest
end

mutual
  /-- A planned read crosses a bare reference before reaching a closed binder boundary. -/
  inductive Risk : Plan → Shape Payload → Prop where
    | reference : Risk plan (.ref name)
    | member (present : member ∈ members) (risk : Risk plan member) : Risk plan (.alternatives members)
    | binder (openBody : (free (.binder name body)).isEmpty = false) (risk : Risk plan body) :
        Risk plan (.binder name body)
    | branch (openBody : (free (.branch payload children)).isEmpty = false)
        (risk : ChildRisk planned 0 children) : Risk (.node observation planned) (.branch payload children)

  /-- A child risk occurs at an existing index with an actual planned subquery. -/
  inductive ChildRisk : List (Nat × Plan) → Nat → List (Shape Payload) → Prop where
    | head (requested : childAt index planned = some plan) (risk : Risk plan child) :
        ChildRisk planned index (child :: rest)
    | tail (risk : ChildRisk planned (index + 1) rest) : ChildRisk planned index (child :: rest)
end

mutual
  /-- The executable node gate detects precisely the independent recursive-read relation. -/
  theorem reaches_exact (plan : Plan) (shape : Shape Payload) : reaches plan shape = true ↔ Risk plan shape := by
    cases shape with
    | empty =>
        constructor
        · simp [reaches]
        · intro risk; cases risk
    | ref name => exact ⟨fun _ => .reference, fun _ => rfl⟩
    | alternatives members =>
        rw [reaches, reachesMembers_exact]
        constructor
        · rintro ⟨member, present, risk⟩; exact .member present risk
        · intro risk; cases risk with | member present risk => exact ⟨_, present, risk⟩
    | binder name body =>
        simp only [reaches, Bool.and_eq_true_iff, Bool.not_eq_true']
        rw [reaches_exact]
        constructor
        · rintro ⟨openBody, risk⟩; exact .binder openBody risk
        · intro risk; cases risk with | binder openBody risk => exact ⟨openBody, risk⟩
    | branch payload children =>
        cases plan with
        | node observation planned =>
            simp only [reaches, Bool.and_eq_true_iff, Bool.not_eq_true']
            rw [reachesChildren_exact]
            constructor
            · rintro ⟨openBody, risk⟩; exact .branch openBody risk
            · intro risk; cases risk with | branch openBody risk => exact ⟨openBody, risk⟩

  /-- Union traversal detects exactly one risky stored member. -/
  theorem reachesMembers_exact (plan : Plan) (members : List (Shape Payload)) :
      reachesMembers plan members = true ↔ ∃ member ∈ members, Risk plan member := by
    cases members with
    | nil => simp [reachesMembers]
    | cons first rest =>
        rw [reachesMembers, Bool.or_eq_true_iff, reaches_exact, reachesMembers_exact]
        simp

  /-- Sparse child traversal detects exactly the indexed recursive-read relation. -/
  theorem reachesChildren_exact (planned : List (Nat × Plan)) (index : Nat) (children : List (Shape Payload)) :
      reachesChildren planned index children = true ↔ ChildRisk planned index children := by
    cases children with
    | nil =>
        constructor
        · simp [reachesChildren]
        · intro risk; cases risk
    | cons child rest =>
        rw [reachesChildren, Bool.or_eq_true_iff, reachesChildren_exact]
        cases requested : childAt index planned with
        | none =>
            simp only [Bool.false_eq_true, false_or]
            constructor
            · exact ChildRisk.tail
            · intro risk
              cases risk with
              | head found risk => simp [requested] at found
              | tail risk => exact risk
        | some plan =>
            rw [reaches_exact]
            constructor
            · rintro (risk | risk)
              · exact .head requested risk
              · exact .tail risk
            · intro risk
              cases risk with
              | head found risk =>
                  have same := Option.some.inj (requested.symm.trans found)
                  subst plan
                  exact .inl risk
              | tail risk => exact .inr risk
end

/-- The source starts each edge query at its actual constructor children. -/
def readsThrough (plan : Plan) (children : List (Shape Payload)) : Bool :=
  match plan with | .node _ planned => reachesChildren planned 0 children

/-- A negative gate rules out every planned read through an unresolved stored reference. -/
theorem negative_gate (observation : Option Need) (planned : List (Nat × Plan)) (children : List (Shape Payload))
    (safe : readsThrough (.node observation planned) children = false) : ¬ ChildRisk planned 0 children := by
  intro risk
  have found := (reachesChildren_exact planned 0 children).mpr risk
  change reachesChildren planned 0 children = false at safe
  rw [safe] at found
  cases found

/-- A closed recursive binder does not require an open-reference fallback. -/
theorem closed_binder (plan : Plan) (name : Nat) (body : Shape Payload)
    (closed : free (.binder name body) = []) : reaches plan (.binder name body) = false := by
  simp [reaches, closed]

/-- An enclosing reference in an open binder's outer union is detected before outer-edge unfolding. -/
theorem enclosing_union_detected (plan : Plan) (name outer : Nat) (different : outer ≠ name)
    (rest : List (Shape Payload)) : reaches plan (.binder name (.alternatives (.ref outer :: rest))) = true := by
  have openBody : (free (.binder name (.alternatives (.ref outer :: rest)))).isEmpty = false := by
    simp [free, freeList, different]
  simp [reaches, openBody, reachesMembers]

/-- The repaired gate selects the existing guard-retention branch; no semantic query is required. -/
theorem detected_guard_retained (original discharged : Edge) (candidates : List (Candidate Edge)) :
    semantic original discharged false true true candidates = .ok [original] :=
  recursive_guard_retained original discharged candidates

/-- The nested binder in the source regression contains an enclosing outer-union reference. -/
theorem open_nested_binder_regression :
    let leaf : Shape Unit := .branch () []
    let nested : Shape Unit := .binder 1 (.alternatives [.ref 0, .branch () [leaf, .ref 1]])
    let plan := Plan.node none [(0, .node (some .refinement) [])]
    reaches plan nested = true := by
  exact enclosing_union_detected _ 1 0 (by decide) _


/-- The actual two-component guard path enters the repaired nested-binder fallback. -/
theorem guarded_outer_edge_regression :
    let leaf : Shape Unit := .branch () []
    let nested : Shape Unit := .binder 1 (.alternatives [.ref 0, .branch () [leaf, .ref 1]])
    readsThrough (Observation.insert [1, 0] .refinement emptyPlan) [leaf, nested] = true := by
  decide +kernel

end MicroCFTA.PruneReads
