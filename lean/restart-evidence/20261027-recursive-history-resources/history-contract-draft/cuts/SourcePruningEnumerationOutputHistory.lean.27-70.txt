inductive OutputHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Output width Typing → Prop where
  /-- The supplied stop decision emits its same cache and endpoint. -/
  | stopped {fuel metadata caller queries before} :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel metadata caller queries before none ⟨some metadata, before, caller, queries⟩
  /-- The supplied done decision emits its same cache and endpoint. -/
  | done {fuel metadata caller queries before} :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel metadata caller queries before (some .done) ⟨none, before, caller, queries⟩
  /-- The actual parked singleton supplies the exact next recursive input. -/
  | parked {fuel metadata caller queries before uv checked parked updated next core output}
      (observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .parked checked (some parked) (some [.ok ((updated, next), core)]))
      (tail : OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel updated caller queries (EnumerationExpandableIndex.frame core parked) next output) :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (fuel + 1) metadata caller queries before (some (.expand uv)) output
  /-- The actual selected cache enters a captured edge and then its false callback. -/
  | ordinary {fuel metadata caller queries before uv checked prepared reached saved action after updated rightCore
        fragment headCaller headQueries headCache recorded callbackCore output}
      (observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .narrowed checked prepared reached saved action (some after)
            (some [.ok ((false, updated), rightCore)]) none)
      (invocation : OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
          fragment headCaller headQueries headCache)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel recorded headCaller headQueries (EnumerationExpandableIndex.frame callbackCore headCache)
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (fuel + 1) metadata caller queries before (some (.expand uv)) output
