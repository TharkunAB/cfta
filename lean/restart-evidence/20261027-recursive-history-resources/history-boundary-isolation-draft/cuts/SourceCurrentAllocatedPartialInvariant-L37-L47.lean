/-- A returned caller retains its actual current context and completed table history. -/
structure Post (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (next : Inventory)
    (before after : Caller width) (final : Memos) : Prop where
  context : Context formulas solver next after final
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  retained : Cache.Extends before.merge after.merge
  fourthRetained : SourceCurrentEmptinessMemo.Extends before.fourth after.fourth

variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
  {inventory next : Inventory} {before middle after : Caller width} {memos final : Memos}
