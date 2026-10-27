private theorem write_replays (uv : Nat) (value : UVarValue Symbol) :
    Replays (EnumerationFlatState.setValue (Guard := EnumGuard) uv value)
      (EnumerationState.setValue uv value) := by
  intro left right result after related observed
  cases result
  have shape := (EnumerationDriver.modify_success
    (fun state => {state with values := state.values.set uv value}) right after).mp observed
  subst after
  refine ⟨{left with values := left.values.set uv value}, rfl, ?_⟩
  exact ⟨related.valid, related.representatives, related.counter,
    congrArg (fun values => values.set uv value) related.values,
    related.obligations, related.recursionAncestry, related.expansionAncestry⟩

private theorem rejection_replays :
    Replays (EnumerationFlatState.reject : Action Symbol EnumGuard Unit)
      (EnumerationState.reject : EnumerateM Symbol EnumGuard Unit) := by
  intro left right result after _related observed
  exact (EnumerationSchedule.reject_unsuccessful right after result observed).elim

private theorem replacement_replays (representativeFuel uv oldHandle newHandle : Nat)
    (scs : List Suspended) :
    Replays
      (if newHandle = oldHandle then (pure () : Action Symbol EnumGuard Unit)
        else EnumerationFlatState.representative uv >>= fun root =>
          EnumerationFlatState.setValue root (.unenumerated (some newHandle) scs))
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol EnumGuard Unit)
        else EnumerationState.representative representativeFuel uv >>= fun root =>
          EnumerationState.setValue root (.unenumerated (some newHandle) scs)) := by
  by_cases same : newHandle = oldHandle
  · simp only [same, ↓reduceIte]
    exact pure_replays ()
  · simp only [same, ↓reduceIte]
    exact bind_replays _ _ _ _ (representative_replays representativeFuel uv)
      (fun root => write_replays root (.unenumerated (some newHandle) scs))

/-- Replay the actual prepared action and retain its exact Empty rejection. -/
theorem prepare_replays [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue value : Value Symbol NativeGuard)
    (heap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (action : EnumerateM Symbol EnumGuard Unit)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata
      nativeFuel representativeFuel uv oldHandle scs oldValue heap =
        .done (value, some action) afterHeap) :
    ∃ flatAction : Action Symbol EnumGuard Unit,
      prepare holeKey fits admits metadata nativeFuel uv oldHandle scs oldValue heap =
        .done (value, some flatAction) afterHeap ∧
      Replays flatAction action ∧
      (value = .empty → flatAction = EnumerationFlatState.reject) := by
  unfold SourcePruningEnumerationAction.prepare at prepared
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      nativeFuel uv oldValue heap with
  | failed fault reached =>
      rw [narrowed] at prepared
      cases prepared
  | done result reached =>
      rw [narrowed] at prepared
      cases result with
      | empty =>
          obtain ⟨pairSame, heapSame⟩ := MergedSourceComparison.Result.done.inj prepared
          obtain ⟨valueSame, actionSome⟩ := Prod.mk.inj pairSame
          have actionSame := Option.some.inj actionSome
          subst value
          subst action
          subst afterHeap
          refine ⟨EnumerationFlatState.reject, ?_, rejection_replays, fun _ => rfl⟩
          simp only [prepare, narrowed]
      | reference name =>
          dsimp only [encodeNode] at prepared
          have actionSome := (Prod.mk.inj (MergedSourceComparison.Result.done.inj prepared).1).2
          cases actionSome
      | node entry edges depth free =>
          dsimp only [encodeNode] at prepared
          obtain ⟨pairSame, heapSame⟩ := MergedSourceComparison.Result.done.inj prepared
          obtain ⟨valueSame, actionSome⟩ := Prod.mk.inj pairSame
          have actionSame := Option.some.inj actionSome
          subst value
          subst action
          subst afterHeap
          refine ⟨(if entry.identity + 1 = oldHandle then pure ()
            else EnumerationFlatState.representative uv >>= fun root =>
              EnumerationFlatState.setValue root (.unenumerated (some (entry.identity + 1)) scs)),
            ?_, replacement_replays representativeFuel uv oldHandle (entry.identity + 1) scs, ?_⟩
          · simp only [prepare, narrowed, encodeNode]
          · intro impossible
            cases impossible
      | union entry members depth free =>
          dsimp only [encodeNode] at prepared
          obtain ⟨pairSame, heapSame⟩ := MergedSourceComparison.Result.done.inj prepared
          obtain ⟨valueSame, actionSome⟩ := Prod.mk.inj pairSame
          have actionSame := Option.some.inj actionSome
          subst value
          subst action
          subst afterHeap
          refine ⟨(if entry.identity + 1 = oldHandle then pure ()
            else EnumerationFlatState.representative uv >>= fun root =>
              EnumerationFlatState.setValue root (.unenumerated (some (entry.identity + 1)) scs)),
            ?_, replacement_replays representativeFuel uv oldHandle (entry.identity + 1) scs, ?_⟩
          · simp only [prepare, narrowed, encodeNode]
          · intro impossible
            cases impossible
      | mu entry body depth ordinary =>
          dsimp only [encodeNode] at prepared
          obtain ⟨pairSame, heapSame⟩ := MergedSourceComparison.Result.done.inj prepared
          obtain ⟨valueSame, actionSome⟩ := Prod.mk.inj pairSame
          have actionSame := Option.some.inj actionSome
          subst value
          subst action
          subst afterHeap
          refine ⟨(if entry.identity + 1 = oldHandle then pure ()
            else EnumerationFlatState.representative uv >>= fun root =>
              EnumerationFlatState.setValue root (.unenumerated (some (entry.identity + 1)) scs)),
            ?_, replacement_replays representativeFuel uv oldHandle (entry.identity + 1) scs, ?_⟩
          · simp only [prepare, narrowed, encodeNode]
          · intro impossible
            cases impossible
