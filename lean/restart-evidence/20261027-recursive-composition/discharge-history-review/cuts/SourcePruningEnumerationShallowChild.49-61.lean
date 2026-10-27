      (value ≠ .empty →
        ∃ (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
          (after : EnumerationState.State Symbol EnumGuard),
          prepareChild scs value = some action ∧ Success action before (.hole before.counter) after ∧
          after = (match value with
            | .node _ _ _ _ =>
                {allocated (some node) before with values :=
                  (allocated (some node) before).values.set before.counter (.unenumerated (some node) scs)}
            | _ => allocated (some node) before) ∧
          after.values[before.counter]? = some (.unenumerated (some node)
            (match value with | .node _ _ _ _ => scs | _ => [])) ∧
          after.counter = before.counter + 1 ∧ after.counter = after.values.length ∧
          PendingRealized heap after)
