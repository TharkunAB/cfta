theorem enter_replays (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv : Nat) (flat : EnumerationFlatState.State Symbol EnumGuard)
    (earlier : EnumerationState.State Symbol EnumGuard)
    (value : Nat × Nat × List Suspended × InternedConstructorTemplates.Value Symbol NativeGuard)
    (after : EnumerationState.State Symbol EnumGuard)
    (related : EnumerationFlatState.Related flat earlier)
    (completed : ExceptT.run (SourcePruningEnumerationEntry.enter heap fuel uv earlier) = [.ok (value, after)]) :
    ∃ next, ExceptT.run (enter heap uv flat) = [.ok (value, next)] ∧
      EnumerationFlatState.Related next after := by
