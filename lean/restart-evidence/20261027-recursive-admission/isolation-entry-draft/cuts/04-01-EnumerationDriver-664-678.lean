structure RenderStable (before after : State Symbol Guard) : Prop where
  safe : Safe after
  counter : after.counter = before.counter
  values : after.values = before.values
  obligations : after.obligations = before.obligations
  classes : ∀ left right, UnionFind.SameClass after.representatives left right ↔ UnionFind.SameClass before.representatives left right

/-- An unchanged rendering state retains all stored data. -/
theorem RenderStable.refl (state : State Symbol Guard) (safe : Safe state) : RenderStable state state :=
  ⟨safe, rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- Rendering preservation composes through consecutive actions. -/
theorem RenderStable.trans (left : RenderStable before middle) (right : RenderStable middle after) :
    RenderStable before after :=
  ⟨right.safe, right.counter.trans left.counter, right.values.trans left.values, right.obligations.trans left.obligations,
