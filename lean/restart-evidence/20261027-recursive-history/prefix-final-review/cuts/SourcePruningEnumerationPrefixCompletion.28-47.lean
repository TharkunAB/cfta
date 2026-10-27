/-- Retain the complete earlier capability and the prefix endpoint's counter and dependency levels.
The finish expression embeds the observation in the earlier proposition.
The recursive worker does not execute this finish expression. -/
def PrefixValid
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (result : Result width Typing) : Prop :=
  (match result with
    | .narrowed _ _ _ _ _ _ _ ordinary => ordinary = none
    | _ => True) ∧
  Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel fuel fuel fuel fuel fuel 0 0 0 0 0 uv caller before memos
    (finish checkEmpty edgesOf 0 0 0 0 0 uv result) ∧
  match result with
  | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
      after.core.counter = before.core.counter ∧
      ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        EnumerationOrder.Stratified after.core level frontier
  | _ => True
