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
