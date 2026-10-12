import MicroCFTA.IntersectSchedule

/-!
# Executed recursive intersection examples

The two recursive inputs accept finite unary chains. The source schedule
constructs one recursive output binder. Its least language is exactly the
intersection of the two original least languages.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- The guard in each intersected example edge is the conjunction of two true guards. -/
def truePayload (symbol : Nat) : Payload Nat := ⟨symbol, fun _ => true = true ∧ true = true⟩

/-- One leaf and one recursive unary alternative. -/
def unaryBody (name : Nat) : Shape (Payload Nat) :=
  .alternatives [.branch (truePayload 0) [], .branch (truePayload 1) [.ref name]]

/-- The least language of finite unary chains. -/
def unaryShape (name : Nat) : Shape (Payload Nat) := .binder name (unaryBody name)

/-- Two separately interned binders have the same complete recursive language. -/
def unaryView : View Nat where
  rows := fun name =>
    if name = 3 then [⟨0, [], fun _ => true⟩, ⟨1, [.ref 1], fun _ => true⟩]
    else if name = 4 then [⟨0, [], fun _ => true⟩, ⟨1, [.ref 2], fun _ => true⟩]
    else []
  body := fun name => if name = 1 then .node 3 else if name = 2 then .node 4 else .empty
  members := fun _ => []
  free := fun input => match input with
    | .ref name => [name]
    | .node 3 => [1]
    | .node 4 => [2]
    | _ => []
  copy := fun input => match input with
    | .mu 1 => unaryShape 101
    | .mu 2 => unaryShape 102
    | .node 3 => unaryBody 101
    | .node 4 => unaryBody 102
    | .ref name => .ref (name + 100)
    | _ => .empty

/-- The source creates one enclosing intersection binder and reuses it at the recursive child. -/
theorem unary_intersection_executes : run unaryView 20 {} (.mu 1) (.mu 2) = .ok (unaryShape 5) := by
  cbv

/-- A repeated recursive identity pair is cut off before its missing environment entries are read. -/
theorem repeated_pair_precedes_lookup :
    lookup (⟨[], [(1, 2)]⟩ : Domain) 1 = none ∧
    run unaryView 1 ⟨[], [(1, 2)]⟩ (.ref 1) (.ref 2) = .ok (.ref 5) := by
  constructor <;> cbv

/-- The same free references fail explicitly when their intersection pair is not enclosing. -/
theorem missing_pair_requires_lookup :
    run unaryView 1 {} (.ref 1) (.ref 2) = .error (.missingBinder 1) := by
  cbv

/-- Independent finite-term syntax for the example language. -/
inductive Unary : Term Nat → Prop where
  | leaf : Unary (.node 0 [])
  | next {term} : Unary term → Unary (.node 1 [term])

/-- The example body either returns its leaf or wraps one supplied recursive member. -/
theorem unaryBody_meaning (environment : Env Nat) (name : Nat) (term : Term Nat) :
    meaning environment (unaryBody name) term ↔
      term = .node 0 [] ∨ ∃ child, term = .node 1 [child] ∧ environment name child := by
  simp only [unaryBody, meaning]
  constructor
  · rintro ⟨⟨shape, member⟩, accepted⟩
    rcases List.mem_cons.mp member with rfl | member
    · rw [meaning] at accepted
      obtain ⟨terms, same, children, _⟩ := accepted
      cases terms with
      | nil => exact Or.inl same
      | cons _ _ => simp [forest] at children
    · have sameShape : shape = .branch (truePayload 1) [.ref name] := by simpa using member
      subst shape
      rw [meaning] at accepted
      obtain ⟨terms, same, children, _⟩ := accepted
      cases terms with
      | nil => simp [forest] at children
      | cons child rest =>
        cases rest with
        | nil => exact Or.inr ⟨child, same, by simpa [forest, meaning] using children⟩
        | cons _ _ => simp [forest] at children
  · rintro (rfl | ⟨child, rfl, accepted⟩)
    · refine ⟨⟨.branch (truePayload 0) [], by simp⟩, ?_⟩
      rw [meaning]
      exact ⟨[], rfl, by simp [forest], rfl, rfl⟩
    · refine ⟨⟨.branch (truePayload 1) [.ref name], by simp⟩, ?_⟩
      rw [meaning]
      exact ⟨[child], rfl, by simpa [forest, meaning] using accepted, rfl, rfl⟩

/-- Every chosen binder name denotes exactly the independent finite unary-chain language. -/
theorem unaryShape_exact (environment : Env Nat) (name : Nat) (term : Term Nat) :
    meaning environment (unaryShape name) term ↔ Unary term := by
  constructor
  · intro accepted
    change meaning environment (.binder name (unaryBody name)) term at accepted
    rw [meaning] at accepted
    apply least_le (fun value => meaning (BinderLanguage.bind environment name value) (unaryBody name)) Unary _ term accepted
    intro output body
    rcases (unaryBody_meaning _ name output).mp body with rfl | ⟨child, rfl, member⟩
    · exact .leaf
    · exact .next (by simpa [BinderLanguage.bind] using member)
  · intro accepted
    induction accepted with
    | leaf =>
      apply (binder_unfold environment name (unaryBody name) _).mpr
      exact (unaryBody_meaning _ name _).mpr (Or.inl rfl)
    | @next child accepted ih =>
      apply (binder_unfold environment name (unaryBody name) _).mpr
      exact (unaryBody_meaning _ name _).mpr (Or.inr ⟨child, rfl, by simpa [BinderLanguage.bind, unaryShape] using ih⟩)

/-- The actual bounded cyclic intersection output accepts every common finite term and only those terms. -/
theorem unary_intersection_exact (environment : Env Nat) (term : Term Nat) :
    run unaryView 20 {} (.mu 1) (.mu 2) = .ok (unaryShape 5) ∧
    (meaning environment (unaryShape 5) term ↔
      meaning environment (unaryView.copy (.mu 1)) term ∧
        meaning environment (unaryView.copy (.mu 2)) term) := by
  refine ⟨unary_intersection_executes, ?_⟩
  change meaning environment (unaryShape 5) term ↔
    meaning environment (unaryShape 101) term ∧ meaning environment (unaryShape 102) term
  simp only [unaryShape_exact, and_self]

end MicroCFTA.IntersectSchedule
