theorem narrowAt_sound [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (guarded : InternedGuardedProbeHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrowAt fits admits fuel key value before = .done result after)
    (term : Term Symbol) (accepted : meaning holds ambient result term) :
    meaning holds ambient value term := by
  obtain ⟨rows, middle, exposed, _built, exactRows⟩ :=
    narrowAt_edges holds ambient fits admits key fuel value before result after ready available closed actual
  obtain ⟨edge, member, _kept, accepted⟩ := (exactRows term).mp accepted
  exact MergedFreshOrdinaryGuardedSoundness.nodeEdges_sound holds ambient fuel value before
    ready.semantic ready.covered guarded available closed rows middle exposed edge member term accepted
