import MicroCFTA.MergedColdBuildLanguage

/-!
# Finite recursive exposure bounds for the raw physical graph

The bound counts Mu exposure on each path. Constructor steps and explicit
unions retain it. Each finite raw graph run has such a bound.
-/
namespace MicroCFTA.MergedColdGraphApprox
open InternedConstructorTemplates InternedProbeProvenance InternedNestedConstruction
open MergedPhysicalComparison MergedPhysicalLanguage MergedColdInterpretation Language

mutual
/-- An accepting run uses at most the supplied number of Mu exposures per path. -/
inductive Approx [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) : Nat → Value Symbol Guard → Term Symbol → Prop where
  | node {entry depth free bound} {edges : List (EdgeValue Symbol Guard)}
      (edge : EdgeValue Symbol Guard) (terms : List (Term Symbol)) :
      edge ∈ edges → Runs state meaning bound edge.children terms →
      meaning edge.entry.key.constraint (.node edge.entry.key.symbol terms) = true →
      Approx state meaning bound (.node entry edges depth free) (.node edge.entry.key.symbol terms)
  | union {entry depth free bound} {members : List (Value Symbol Guard)} {member term} :
      member ∈ members → Approx state meaning bound member term →
      Approx state meaning bound (.union entry members depth free) term
  | unfold {entry body depth ordinary bound result after term} :
      InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done result after →
      Approx state meaning bound result term → Approx state meaning (bound + 1) (.mu entry body depth ordinary) term

/-- Ordered child runs use one common exposure bound. -/
inductive Runs [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) : Nat → List (Value Symbol Guard) → List (Term Symbol) → Prop where
  | nil {bound} : Runs state meaning bound [] []
  | cons {bound value term values terms} : Approx state meaning bound value term →
      Runs state meaning bound values terms → Runs state meaning bound (value :: values) (term :: terms)
end

/-- The mutual child relation has exactly the usual pointwise meaning. -/
theorem Runs.all [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard}
    {meaning : Guard → Term Symbol → Bool} {bound values terms}
    (runs : Runs state meaning bound values terms) : All₂ (Approx state meaning bound) values terms := by
  induction runs using Runs.rec (motive_1 := fun _ _ _ _ => True) with
  | node | union | unfold => trivial
  | nil => exact .nil
  | cons head tail ihHead ihTail => exact .cons head ihTail

/-- Pointwise bounded child runs give the mutual child relation. -/
theorem Runs.ofAll [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard}
    {meaning : Guard → Term Symbol → Bool} {bound values terms}
    (runs : All₂ (Approx state meaning bound) values terms) : Runs state meaning bound values terms := by
  induction runs with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- Every exposure bound obeys the ordinary constructor language laws. -/
theorem laws [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (bound : Nat) : Laws (Approx state meaning bound) meaning := by
  constructor
  · intro term accepted; cases accepted
  · intro entry edges depth free term
    constructor
    · intro accepted; cases accepted with
      | node edge terms member runs allowed => exact ⟨edge, member, terms, rfl, runs.all, allowed⟩
    · rintro ⟨edge, member, terms, rfl, runs, allowed⟩
      exact .node edge terms member (Runs.ofAll runs) allowed
  · intro entry members depth free term
    constructor
    · intro accepted; cases accepted with | union member accepted => exact ⟨_, member, accepted⟩
    · rintro ⟨member, present, accepted⟩; exact .union present accepted

/-- The actual completed Mu read supplies precisely one bounded exposure step. -/
theorem mu_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (bound : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary result : Value Symbol Guard)
    (after : State Symbol Guard)
    (done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done result after)
    (term : Term Symbol) :
    Approx state meaning (bound + 1) (.mu entry body depth ordinary) term ↔ Approx state meaning bound result term := by
  constructor
  · intro accepted
    cases accepted with
    | unfold computed accepted => cases done.symm.trans computed; exact accepted
  · exact .unfold done

/-- A larger bound retains every finite exposure derivation. -/
theorem mono [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (bound : Nat) (value : Value Symbol Guard) (term : Term Symbol)
    (accepted : Approx state meaning bound value term) :
    ∀ later, bound ≤ later → Approx state meaning later value term := by
  induction accepted using Approx.rec
    (motive_2 := fun bound values terms _ => ∀ later, bound ≤ later → Runs state meaning later values terms) with
  | node edge terms member runs allowed ih => intro later enough; exact .node edge terms member (ih later enough) allowed
  | union member accepted ih => intro later enough; exact .union member (ih later enough)
  | @unfold entry body depth ordinary bound result after term done accepted ih =>
      intro later enough
      cases later with
      | zero => omega
      | succ later => exact .unfold done (ih later (by omega))
  | nil => exact .nil
  | cons head tail ihHead ihTail => rename_i later enough; exact .cons (ihHead later enough) (ihTail later enough)

/-- A bounded exposure derivation is an actual finite raw graph run. -/
theorem sound [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (bound : Nat) (value : Value Symbol Guard) (term : Term Symbol)
    (accepted : Approx state meaning bound value term) : EpsilonUnion.Accepts (graph state meaning) value term := by
  induction accepted using Approx.rec
    (motive_2 := fun _ values terms _ => All₂ (EpsilonUnion.Accepts (graph state meaning)) values terms) with
  | node edge terms member runs allowed ih =>
      exact .node ⟨edge.entry.key.symbol, edge.children, meaning edge.entry.key.constraint⟩ terms
        (List.mem_map.mpr ⟨edge, member, rfl⟩) ih allowed
  | union member accepted ih => exact .reference member ih
  | unfold done accepted ih => exact .reference (by simp [graph, successors, done]) ih
  | nil => exact .nil
  | cons head tail ihHead ihTail => exact .cons ihHead ihTail

/-- Every finite raw graph run has a finite Mu exposure bound. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (term : Term Symbol)
    (accepted : EpsilonUnion.Accepts (graph state meaning) value term) :
    ∃ bound, Approx state meaning bound value term := by
  induction accepted using EpsilonUnion.Accepts.rec
    (motive_2 := fun values terms _ => ∃ bound, All₂ (Approx state meaning bound) values terms) with
  | @reference root target term member accepted ih =>
      obtain ⟨bound, accepted⟩ := ih
      cases root with
      | empty | reference | node => simp [graph, successors] at member
      | union entry members depth free => exact ⟨bound, .union member accepted⟩
      | mu entry body depth ordinary =>
          cases done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state with
          | pending key after => simp [graph, successors, done] at member
          | done result after =>
              have same : target = result := by simpa [graph, successors, done] using member
              subst target
              exact ⟨bound + 1, .unfold done accepted⟩
  | @node root edge terms member runs allowed ih =>
      obtain ⟨bound, runs⟩ := ih
      cases root with
      | empty | reference | union | mu => simp [graph, constructorRows] at member
      | node entry edges depth free =>
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          exact ⟨bound, .node original terms present (Runs.ofAll runs) allowed⟩
  | nil => exact ⟨0, .nil⟩
  | @cons value term values terms head tail ihHead ihTail =>
      obtain ⟨first, accepted⟩ := ihHead
      obtain ⟨rest, runs⟩ := ihTail
      exact ⟨max first rest, .cons (mono state meaning first value term accepted _ (Nat.le_max_left _ _))
        (runs.imp (fun value term accepted => mono state meaning rest value term accepted _ (Nat.le_max_right _ _)))⟩

/-- Raw graph acceptance is exactly finite bounded Mu exposure. -/
theorem exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph state meaning) value term ↔ ∃ bound, Approx state meaning bound value term :=
  ⟨complete state meaning value term, fun ⟨bound, accepted⟩ => sound state meaning bound value term accepted⟩

end MicroCFTA.MergedColdGraphApprox
