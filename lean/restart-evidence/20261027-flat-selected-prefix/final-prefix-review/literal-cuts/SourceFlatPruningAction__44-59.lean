/-- Retain native effects and compare all captured rows at the actual entry cores. -/
def PreparedRelated (flatCore : EnumerationFlatState.State Symbol EnumGuard)
    (earlierCore : EnumerationState.State Symbol EnumGuard)
    (flat : MergedSourceComparison.Result Symbol NativeGuard
      (Value Symbol NativeGuard × Option (Action Symbol EnumGuard Unit)))
    (earlier : MergedSourceComparison.Result Symbol NativeGuard
      (Value Symbol NativeGuard × Option (EnumerateM Symbol EnumGuard Unit))) : Prop :=
  flat.state = earlier.state ∧
    match flat, earlier with
    | .failed first _, .failed second _ => first = second
    | .done (value, first) _, .done (oldValue, second) _ =>
        value = oldValue ∧ match first, second with
        | none, none => True
        | some action, some oldAction => Results Related (action flatCore) (oldAction earlierCore)
        | _, _ => False
    | _, _ => False
