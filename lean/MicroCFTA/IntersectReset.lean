import MicroCFTA.IntersectInput
import MicroCFTA.IntersectProgress

/-!
# The finite-payload requirement for closed-environment reset

The existing payload interface permits a binder whose body is the same binder.
The source represents recursion with explicit references instead. This model
satisfies the cached free-variable equations, but reset repeats its top-level
problem forever. Thus those equations cannot prove source termination without
the finite lexical-payload representation invariant.
-/
namespace MicroCFTA.IntersectSchedule.ResetBoundary
open Language Binding BinderLanguage

/-- This graph deliberately uses a cyclic payload instead of a recursive reference. -/
def cyclicView : View Nat where
  rows := fun _ => []
  body := Input.mu
  members := fun _ => []
  free := fun input => match input with
    | .ref name => [name]
    | _ => []
  copy := fun _ => .empty

/-- Cached free-variable equations alone do not exclude cyclic binder payloads. -/
theorem cyclic_free_correct : FreeCorrect cyclicView := by
  constructor
  · rfl
  · intro name; rfl
  · intro bound name; simp [cyclicView]
  · intro node name; simp [cyclicView]
  · intro node name; simp [cyclicView]

/-- The local progress measure also permits these impossible source binder payloads. -/
def cyclicLocalWeight : LocalWeight cyclicView where
  value := fun input => match input with
    | .mu _ => 0
    | .node _ => 2
    | _ => 1
  binder := by intro name; rfl
  reference := by intro name; rfl
  positive := by intro node; change 0 < 2; decide
  child := by intro node row member; cases member
  member := by intro node child member; cases member

/-- Two source steps reopen the same problem after resetting the remembered pair. -/
theorem cyclic_reset_step (fuel : Nat) :
    run cyclicView (fuel + 2) {} (.mu 0) (.mu 1) =
      (run cyclicView fuel {} (.mu 0) (.mu 1)).map (maybeMu (pair (.mu 0) (.mu 1))) := by
  rw [run.eq_def]
  simp only [closed, cyclicView, greater, tag, identity]
  simp
  rw [run.eq_def]
  simp [closed, extend]

/-- The repeated reset exhausts every finite execution bound. -/
theorem cyclic_reset_exhausts (fuel : Nat) :
    run cyclicView fuel {} (.mu 0) (.mu 1) = .error .fuelExhausted := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        rw [show fuel + 1 + 1 = fuel + 2 by omega, cyclic_reset_step, ih fuel (by omega)]
        rfl

/-- The cyclic graph cannot satisfy any finite structural binder-body weight. -/
theorem cyclic_has_no_body_weight :
    ¬ ∃ weight : Input → Nat, ∀ name, weight (cyclicView.body name) < weight (.mu name) := by
  rintro ⟨weight, decreases⟩
  exact Nat.lt_irrefl _ (decreases 0)

/-- A cyclic payload without a constructor has no finite accepted input term. -/
theorem cyclic_no_derivation (rank name : Nat) (term : Term Nat) :
    ¬ InputDerivation cyclicView (.mu name) rank term := by
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro accepted
    cases accepted with
    | binder body less => exact ih _ less body

/-- Only binder and reference payloads are reachable in this graph. -/
def cyclicValid : Input → Prop
  | .mu _ | .ref _ => True
  | _ => False

/-- Even exact independent least input semantics does not supply reset termination. -/
def cyclicFiniteInput : FiniteInput cyclicView where
  valid := cyclicValid
  representative := Input.mu
  identity_exact := by
    intro input valid nonempty
    cases input <;> simp_all [cyclicValid, identity, inputRepresentative]
  body_valid := by intro name valid; trivial
  reference_valid := by intro name valid; trivial
  row_valid := by intro name valid; exact False.elim valid
  union_valid := by intro name valid; exact False.elim valid
  copy_exact := by
    intro input valid isClosed environment
    funext term
    apply propext
    cases input with
    | empty | node | union => exact False.elim valid
    | mu name =>
      simp only [cyclicView, meaning]
      constructor
      · exact False.elim
      · rintro ⟨rank, accepted⟩; exact cyclic_no_derivation rank name term accepted
    | ref name =>
      simp only [cyclicView, meaning]
      constructor
      · exact False.elim
      · rintro ⟨rank, accepted⟩
        exact cyclic_no_derivation rank name term ((input_derivation_reference cyclicView name rank term).mp accepted)

end MicroCFTA.IntersectSchedule.ResetBoundary
