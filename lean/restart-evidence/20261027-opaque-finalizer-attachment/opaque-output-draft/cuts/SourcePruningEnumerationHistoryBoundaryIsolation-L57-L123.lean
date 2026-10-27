theorem ResourceHistory.isolated_boundary
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (held heldHandle : Nat) (value : Node)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    IsolatedPending held heldHandle output.cache.core ∧
      lookupNode output.caller.checked.native.machine.heap heldHandle = some value := by
  induction history generalizing held heldHandle value with
  | stopped _ => exact ⟨isolated, decoded⟩
  | done _ => exact ⟨isolated, decoded⟩
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed _tail ih =>
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have prefixIsolated := SourcePruningEnumerationSelectedStep.prefix_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos held heldHandle value admission.1 isolated decoded boundary chosen valid
      rw [observed] at prefixIsolated
      have full := valid.2.1
      rw [observed] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      have cacheSame : parked = cached := Option.some.inj same
      subst cached
      have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
          [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
      obtain ⟨metadataSame, nextSame, returnedCore⟩ := restart_row_fields
        stop order metadata updated parked checked core next rows
      have coreEq : core = parked.core := returnedCore.trans coreSame.symm
      have framed : EnumerationExpandableIndex.frame core parked = parked := by
        rw [coreEq]
        cases parked
        rfl
      have tailNext : next = SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame core parked) := by
        rw [metadataSame, framed]
        exact nextSame
      have tailIsolated : IsolatedPending held heldHandle (EnumerationExpandableIndex.frame core parked).core := by
        rw [framed]
        exact prefixIsolated
      exact ih held heldHandle value tailNext tailIsolated decoded boundary
  | @ordinary fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed prefixPost _invocation receipt _callbackAdmission callback _tail ih =>
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have different := packet_restart_ne formulas solver inventory caller memos metadata before
        held heldHandle uv value stop order admission.1 isolated decoded boundary chosen
      have prefixIsolated := SourcePruningEnumerationSelectedStep.prefix_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos held heldHandle value admission.1 isolated decoded boundary chosen valid
      rw [observed] at prefixIsolated
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have returnedIsolated := receipt.isolated_after_callback graph templates workFuel (false, recorded)
        callbackCore prefixIsolated (Ne.symm different) callbackSuccess
      obtain ⟨_entered, _handle, _scs, _parent, _edge, _headSeed, _inherited,
        _headInventory, _actualHeadCaller, _headMemos, _headBound,
        _original, _entry, _enteredPacket, headPost, _captured, completed⟩ := receipt
      have fullPost := prefixPost.trans (headPost.trans completed.post)
      have returnedDecoded := lookupNode_keeps _ _ fullPost.effects.keeps heldHandle value decoded
