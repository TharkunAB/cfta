structure RenderStable (before after : State Symbol Guard) : Prop where
  safe : Safe after
  counter : after.counter = before.counter
  values : after.values = before.values
  obligations : after.obligations = before.obligations
  classes : ∀ left right, UnionFind.SameClass after.representatives left right ↔ UnionFind.SameClass before.representatives left right
