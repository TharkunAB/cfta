theorem getValue_replays (fuel uv : Nat) :
    Replays (Symbol := Symbol) (Guard := Guard)
      (getValue uv) (EnumerationState.getValue fuel uv) := by
  apply bind_replays _ _ _ _ (representative_replays fuel uv)
  intro root flat earlier value after related observed
  simp only [EnumerationCorrectness.Success, EnumerationState.rawValue, Bind.bind,
    get, getThe, MonadStateOf.get, StateT.bind, StateT.get, ExceptT.bind,
    ExceptT.pure, ExceptT.bindCont, ExceptT.mk, Pure.pure,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, ExceptT.run] at observed
  cases stored : earlier.values[root]? with
  | none =>
      simp only [stored] at observed
      change Except.ok (value, after) ∈ [Except.error EnumerationState.Error.invalidSlot] at observed
      simp only [List.mem_singleton] at observed
      cases observed
  | some found =>
      have same : value = found ∧ after = earlier := by
        simp only [stored] at observed
        change Except.ok (value, after) ∈ [Except.ok (found, earlier)] at observed
        simpa only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] using observed
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨flat, by simp [rawValue, related.values, stored], related⟩

/-- Render the same partial term with structural fuel and direct slot reads. -/
def expandPartial (graph : EnumerationState.Graph Symbol Guard) : Nat → Fragment Symbol →
    Action Symbol Guard (Term (EnumerationState.PartialSymbol Symbol))
  | 0, _ => failure .fuelExhausted
  | fuel + 1, .node symbol children => do
      pure (.node (.concrete symbol) (← children.mapM (expandPartial graph fuel)))
  | fuel + 1, .hole uv => do
      match ← getValue uv with
      | .enumerated fragment => expandPartial graph fuel fragment
      | .unenumerated (some node) [] =>
          match graph.node node with
          | .recursive _ => pure (.node .truncated [])
          | _ => pure (.node (.hole uv) [])
      | _ => pure (.node (.hole uv) [])

/-- Every successful old rendering has the same partial term and related core. -/
theorem expandPartial_replays (graph : EnumerationState.Graph Symbol Guard)
    (fuel : Nat) (fragment : Fragment Symbol) :
    Replays (expandPartial graph fuel fragment) (EnumerationState.expandPartial graph fuel fragment) := by
  induction fuel generalizing fragment with
  | zero =>
      intro flat earlier value after _ observed
      exact (EnumerationCorrectness.success_failure .fuelExhausted earlier after value observed).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Replays
            (children.mapM (expandPartial graph fuel) >>= fun terms => pure (Term.node (.concrete symbol) terms))
            (children.mapM (EnumerationState.expandPartial graph fuel) >>= fun terms =>
              pure (Term.node (.concrete symbol) terms))
          exact bind_replays _ _ _ _
            (mapM_replays _ _ (fun child => ih child) children)
            (fun terms => pure_replays (Term.node (.concrete symbol) terms))
      | hole uv =>
          apply bind_replays _ _ _ _ (getValue_replays (fuel + 1) uv)
          intro value
          cases value with
          | enumerated fragment => exact ih fragment
          | eliminated => exact pure_replays _
          | unenumerated node scs =>
              cases node with
              | none => exact pure_replays _
              | some node =>
                  cases scs with
                  | cons first rest => exact pure_replays _
                  | nil =>
                      dsimp only
                      cases graph.node node <;> exact pure_replays _

end MicroCFTA.EnumerationFlatPartial
