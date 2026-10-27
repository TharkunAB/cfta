        returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before (fuel + 1) seed ceiling)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory workFuel uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
      (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed)
            (some [.ok ((false, updated), rightCore)]) none)
      (prefixPost : Post formulas solver ordinaryInventory caller ordinaryCaller ordinaryMemos)
      (invocation : SourcePruningEnumerationHookInvocation.OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel uv edgesOf ordinaryCaller narrowed ordinaryMemos.query
          fragment headCaller returnedMemos.query headCache)
      (receipt : OrdinaryHistoryReceipt formulas solver updated checkEmpty workFuel uv ordinaryInventory
        ordinaryCaller ordinaryMemos narrowed fragment headCaller headCache returnedInventory returnedMemos)
      (callbackAdmission : RecursiveCallbackAdmission formulas solver returnedInventory headCaller returnedMemos updated
        headCache uv fragment fuel callbackSeed callbackCeiling)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel returnedInventory headCaller returnedMemos recorded (EnumerationExpandableIndex.frame callbackCore headCache)
          callbackSeed callbackCeiling
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output
