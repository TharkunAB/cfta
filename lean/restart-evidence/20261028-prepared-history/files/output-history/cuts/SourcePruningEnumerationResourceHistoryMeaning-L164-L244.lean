theorem ResourceHistoryWithArity.sound
    (history : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : Canonical before.core)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient output.caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment output.cache.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core := by
  revert actualNext canonical discharged
  induction history with
  | stopped _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
      exact satisfied
  | done _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
      exact satisfied
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed tail _ih =>
      intro actualNext _canonical discharged
      obtain ⟨_handle, _bucket, _value, _stored, _decoded, _boundary, _created, _retained,
        _outputDecoded, impossible⟩ := parked_tail_created_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel fuel
        inventory caller memos metadata updated before parked uv checked core next tailSeed tailCeiling output
        admission.1 actualNext.symm valid observed tail.forget
      exact False.elim (impossible discharged)
  | @ordinary fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed _prefixPost invocation receipt _callbackAdmission callback tail ih =>
      intro actualNext canonical discharged
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have narrowedCanonical := SourcePruningEnumerationSelectedStep.prefix_canonical
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos canonical valid
      rw [observed] at narrowedCanonical
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have callbackCanonical := receipt.forget.canonical_after_callback graph templates workFuel
        (false, recorded) callbackCore narrowedCanonical callbackSuccess
      have tailMeaning := ih rfl callbackCanonical discharged
      have ready := packet_selected_ready formulas solver inventory stop order metadata caller memos before uv
        admission.1 chosen
      obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := admission.1.valid
      have prefixMeaning := SourcePruningEnumerationSelectedStep.prefix_semantics
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.context ready realized valid
      rw [observed] at prefixMeaning
      obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, localHeadCaller,
        headMemos, headBound, original, entry, enteredPacket, headPost, _captured, completed, ownArity⟩ := receipt
      have entrySuccess : Success (SourcePruningEnumerationEntry.enter
          ordinaryCaller.checked.native.machine.heap workFuel uv) narrowed.core
          (uv, handle, scs, decoded) entered.core := by
        rw [Success, entry]
        exact List.mem_singleton_self _
      have nonterminal := invocation.entry_nonterminal entrySuccess
      have retained := SourcePruningEnumerationOpaqueEvent.completed_head_output_retained
        headSeed inherited formulas solver headInventory localHeadCaller headMemos updated entered checkEmpty
        uv scs edge headBound fragment headCaller returnedMemos.query headCache returnedInventory returnedMemos
        completed holeKey fits admits graph templates edgesOf stop order workFuel fuel recorded callbackCore
        callbackSeed callbackCeiling output callback tail.forget discharged
      obtain ⟨_originalHandle, _parentEntry, _storedEdges, _depth, _free, _stored, _decoded,
        _selected, localMeaning⟩ :=
        SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.sound_ordinary_callback_input
          original entrySuccess enteredPacket headPost completed callbackSuccess narrowedCanonical
          nonterminal ownArity retained
      intro ambient assignment satisfied
      have callbackSatisfied := tailMeaning ambient assignment satisfied
      have narrowedSatisfied := (localMeaning ambient assignment callbackSatisfied).1
      exact prefixMeaning ambient _ assignment narrowedSatisfied

end MicroCFTA.SourcePruningEnumerationRecursive
