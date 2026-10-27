
/-- Every operation tag retains its actual original resource inputs and reached callback input. -/
inductive ResourceHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel : Nat) :
    Nat → Inventory → Caller (bits + 2) → Memos → Metadata Typing → Cached → Seed → Nat →
      Option Next → Output (bits + 2) Typing → Prop where
  /-- A supplied stop retains its own admitted cache and metadata. -/
  | stopped {fuel inventory caller memos metadata before seed ceiling}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before fuel seed ceiling) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos metadata before seed ceiling none ⟨some metadata, before, caller, memos.query⟩
  /-- A supplied done decision retains its own admitted cache. -/
  | done {fuel inventory caller memos metadata before seed ceiling}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before fuel seed ceiling) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos metadata before seed ceiling (some .done) ⟨none, before, caller, memos.query⟩
  /-- An actual parked restart uses the same native caller and full memo state. -/
  | parked {fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
        tailSeed tailCeiling output}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before (fuel + 1) seed ceiling)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory workFuel uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
      (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .parked checked (some parked) (some [.ok ((updated, next), core)]))
      (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos updated (EnumerationExpandableIndex.frame core parked) tailSeed tailCeiling next output) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output
  /-- The actual ordinary invocation retains entry, full head receipts and its admitted false callback. -/
  | ordinary {fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
        ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
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
