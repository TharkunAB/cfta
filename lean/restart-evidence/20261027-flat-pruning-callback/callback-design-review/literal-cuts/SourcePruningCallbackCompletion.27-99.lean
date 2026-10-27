    (allocated : FragmentBound before.counter fragment)
    (bounded : ∀ group ∈ metadata.pending, ∀ entry ∈ group, entry.2 < before.counter) :
    ∃ fuel result after,
      Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing := by
  have completed : ∃ fuel result after,
      Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier := by
    cases templates with
    | nil =>
        refine ⟨0, (false, {metadata with types := updatedTypes metadata uv (.inl fragment)}),
          before, ?_, .refl before safe, .refl before, stratified⟩
        rw [recordTypes_empty]
        exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
    | cons first rest =>
        obtain ⟨fuel, observed, after, observation, stable, frame, ordered⟩ :=
          SourcePruningOracle.oracle_inl_complete graph (first :: rest) level frontier metadata.pending
            uv fragment before safe stratified allocated bounded
        refine ⟨fuel, (observed.1, {metadata with pending := observed.2, types := updatedTypes metadata uv (.inl fragment)}),
          after, ?_, stable, frame, ordered⟩
        change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv (.inl fragment) >>= _)
          before _ after
        exact (success_bind _ _ _ _ _).mpr ⟨observed, after, observation,
          (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  obtain ⟨fuel, result, after, success, stable, frame, ordered⟩ := completed
  exact ⟨fuel, result, after, success, stable, frame, ordered,
    recordTypes_metadata graph templates fuel metadata uv (.inl fragment) before after result success⟩

/-- A completed fragment event keeps every returned pending ID allocated. -/
theorem recordTypes_inl_bounded (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat) (metadata : Metadata Typing)
    (uv : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (result : Bool × Metadata Typing) (safe : Safe before)
    (allocated : FragmentBound before.counter fragment)
    (bounded : ∀ group ∈ metadata.pending, PendingBound before.counter group)
    (success : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after) :
    ∀ group ∈ result.2.pending, PendingBound after.counter group := by
  cases templates with
  | nil =>
      rw [recordTypes_empty] at success
      obtain ⟨rfl, rfl⟩ := (success_pure _ result before after).mp success
      exact bounded
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv (.inl fragment) >>= fun observed =>
        pure (observed.1, {metadata with pending := observed.2, types := updatedTypes metadata uv (.inl fragment)}))
        before result after at success
      obtain ⟨observed, middle, observation, final⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨rfl, rfl⟩ := (success_pure _ result middle after).mp final
      exact SourcePruningOracle.oracle_inl_bounded graph (first :: rest) fuel metadata.pending uv fragment
        before after observed safe allocated bounded observation

/-- Fragment callback completion also supplies the pending-ID bounds for its next call. -/
theorem recordTypes_inl_complete_bounded (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (level : Nat → Nat) (frontier : Nat)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment Symbol)
    (before : State Symbol Guard) (safe : Safe before)
    (stratified : Stratified before level frontier)
    (allocated : FragmentBound before.counter fragment)
    (bounded : ∀ group ∈ metadata.pending, PendingBound before.counter group) :
    ∃ fuel result after,
      Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ group ∈ result.2.pending, PendingBound after.counter group := by
  obtain ⟨fuel, result, after, success, stable, frame, ordered, types, openHoles, typing⟩ :=
    recordTypes_inl_complete graph templates level frontier metadata uv fragment before safe stratified allocated bounded
  exact ⟨fuel, result, after, success, stable, frame, ordered, types, openHoles, typing,
    recordTypes_inl_bounded graph templates fuel metadata uv fragment before after result safe allocated bounded success⟩

end MicroCFTA.SourcePruningRecordTypes
