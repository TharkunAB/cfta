/-- An actual narrowing result denotes exactly its accepted filtered source edges. -/
theorem narrowAt_edges [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrowAt fits admits fuel key value before = .done result after) :
    ∃ rows middle,
      MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows middle ∧
      run (makeNode (rows.filter (keeps fits admits key))) middle = (result, after) ∧
      ∀ term, meaning holds ambient result term ↔
        ∃ edge ∈ rows, keeps fits admits key edge = true ∧ edgeMeaning holds ambient edge term := by
