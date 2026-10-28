/-- Original references and graph-bearing classes reach the same output through its actual history. -/
theorem ResourceHistory.carriers_output
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (references : ReferencesCarry before.core) :
    PreservesCarriers before.core output.cache.core ∧ ReferencesCarry output.cache.core := by
  induction history with
  | stopped _ => exact ⟨.refl _, references⟩
  | done _ => exact ⟨.refl _, references⟩
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed _tail ih =>
      have prefixFacts := SourcePruningEnumerationSelectedStep.prefix_carriers
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.safe.1.total references valid
      rw [observed] at prefixFacts
      have full := valid.2.1
      rw [observed] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      have cacheSame : parked = cached := Option.some.inj same
      subst cached
      have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
          [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
      have returnedCore : core = parked.core := by
        change (if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
          else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), checked)]) =
            [Except.ok ((updated, next), core)] at rows
        split at rows
        · cases rows
        · have sameCore : checked = core := congrArg Prod.snd (Except.ok.inj (List.cons.inj rows).1)
          exact sameCore.symm.trans coreSame.symm
      have beforeTail : PreservesCarriers before.core core := by
        rw [returnedCore]
        exact prefixFacts.2.1
      have tailReferences : ReferencesCarry core := by
        rw [returnedCore]
        exact prefixFacts.2.2
      obtain ⟨tailCarriers, outputReferences⟩ := ih tailReferences
      exact ⟨beforeTail.trans tailCarriers, outputReferences⟩
  | @ordinary fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed _prefixPost _invocation receipt _callbackAdmission callback _tail ih =>
      have prefixFacts := SourcePruningEnumerationSelectedStep.prefix_carriers
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.safe.1.total references valid
      rw [observed] at prefixFacts
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have callbackFacts := receipt.carriers_after_callback graph templates workFuel (false, _) callbackCore
        prefixFacts.2.2 callbackSuccess
      obtain ⟨tailCarriers, outputReferences⟩ := ih callbackFacts.2.2.1
      exact ⟨prefixFacts.2.1.trans (callbackFacts.2.1.trans tailCarriers), outputReferences⟩

end MicroCFTA.SourcePruningEnumerationRecursive
