import MicroCFTA.EnumerationPendingAssignment

namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationDependencies
variable {Symbol : Type}
set_option autoImplicit false

/-- Equal base choices give equal finite evaluation on a dependency-closed set. -/
theorem evaluateSlotsWith_congr_on
    (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (left right : Nat → Term Symbol) (kept : Nat → Prop)
    (dependencies : ∀ uv, kept uv → ∀ fragment,
      values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, HasHole fragment hole → kept hole)
    (agree : ∀ uv, kept uv → left uv = right uv) :
    ∀ fuel uv, kept uv →
      evaluateSlotsWith values roots left fuel uv = evaluateSlotsWith values roots right fuel uv := by
  intro fuel
  induction fuel with
  | zero =>
      intro uv inside
      exact agree uv inside
  | succ fuel ih =>
      intro uv inside
      cases stored : values[roots uv]? with
      | none =>
          simpa only [evaluateSlotsWith, stored] using agree uv inside
      | some value =>
          cases value with
          | eliminated | unenumerated _ _ =>
              simpa only [evaluateSlotsWith, stored] using agree uv inside
          | enumerated fragment =>
              simp only [evaluateSlotsWith, stored]
              apply EnumerationAssignment.fill_holes_congr
              intro hole present
              exact ih hole (dependencies uv inside fragment stored hole present)

end MicroCFTA.EnumerationPendingAssignment
