
/-- Ordered caller stages compose even when they compute different inventories. -/
theorem Post.trans (first : Post formulas solver inventory before middle memos)
    (last : Post formulas solver next middle after final) : Post formulas solver next before after final :=
  ⟨last.context, first.effects.trans last.effects, Cache.extends_trans first.retained last.retained,
    fun key value found => last.fourthRetained key value (first.fourthRetained key value found)⟩

/-- Protocol changes retain a reflexive physical history and the supplied phase law. -/
theorem Post.rebase (context : Context formulas solver inventory before memos)
    (checked : after.checked = before.checked) (merge : after.merge = before.merge)
    (fourth : after.fourth = before.fourth)
