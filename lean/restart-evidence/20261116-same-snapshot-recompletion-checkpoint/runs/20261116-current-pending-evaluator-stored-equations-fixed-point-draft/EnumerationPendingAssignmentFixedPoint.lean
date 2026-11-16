import MicroCFTA.EnumerationPendingAssignment

namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationSchedule EnumerationDependencies
variable {Symbol Guard : Type}
set_option autoImplicit false

/-- An assignment that satisfies stored equations is fixed at every finite evaluator fuel. -/
theorem evaluateSlotsWith_fixed_of_stored_equations
    (state : State Symbol Guard) (roots : Nat → Nat)
    (paths : Roots state.representatives roots) (rho : Nat → Term Symbol)
    (aliases : UnionFind.Satisfies state.representatives rho)
    (equations : ∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
      fill rho fragment = rho slot) :
    ∀ fuel uv, evaluateSlotsWith state.values roots rho fuel uv = rho uv := by
  intro fuel
  induction fuel with
  | zero =>
      intro uv
      rfl
  | succ fuel ih =>
      intro uv
      cases stored : state.values[roots uv]? with
      | none =>
          simp only [evaluateSlotsWith, stored]
      | some value =>
          cases value with
          | eliminated | unenumerated _ _ =>
              simp only [evaluateSlotsWith, stored]
          | enumerated fragment =>
              simp only [evaluateSlotsWith, stored]
              obtain ⟨size, path⟩ := paths uv
              have filled : fill (evaluateSlotsWith state.values roots rho fuel) fragment =
                  fill rho fragment :=
                EnumerationAssignment.fill_holes_congr _ _ fragment (fun hole _ => ih hole)
              have atRoot := equations (roots uv) fragment stored
              have sameValue := aliases uv (roots uv) (UnionFind.sameClass_root path)
              exact filled.trans (atRoot.trans sameValue.symm)

end MicroCFTA.EnumerationPendingAssignment
