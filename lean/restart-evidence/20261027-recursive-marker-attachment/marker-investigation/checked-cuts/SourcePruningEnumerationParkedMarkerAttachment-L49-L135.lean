/-- An actual parked prefix creates an isolated marker that survives its own remaining admitted history. -/
theorem parked_tail_created_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (inventory : Inventory) (caller : Caller (bits + 2))
    (memos : Memos) (metadata updated : Metadata Typing) (before parked : Cached)
    (uv : Nat) (checked core : Core) (next : Option Next)
    (tailSeed : SourcePruningEnumerationIncomingReservation.Seed) (tailCeiling : Nat)
    (output : Output (bits + 2) Typing)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory workFuel uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .parked checked (some parked) (some [.ok ((updated, next), core)]))
    (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos updated (EnumerationExpandableIndex.frame core parked)
        tailSeed tailCeiling next output) :
    ∃ handle bucket value,
      before.core.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      IsolatedPending uv handle parked.core ∧ IsolatedPending uv handle output.cache.core ∧
      lookupNode output.caller.checked.native.machine.heap handle = some value ∧
      ¬SourcePruningEnumerationRendering.Discharged output.cache.core := by
  obtain ⟨ready, incoming, _selectedValue⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  have full := valid.2.1
  rw [observed] at full
  obtain ⟨handle, bucket, readAfter, reading, checking, cached, same, coreSame,
    _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
  have cacheSame : parked = cached := Option.some.inj same
  subst cached
  have readSuccess : Success (getValue workFuel uv) before.core
      (.unenumerated (some handle) bucket) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have frame := (EnumerationCompressionFrame.getValue_frame workFuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
  have readReady := (EnumerationDriver.getValue_ready workFuel uv before.core readAfter _ ready readSuccess).1
  have readStored := (EnumerationDriver.getValue_root workFuel uv before.core readAfter _
    ready.safe ready.inside ready.root readSuccess).2.2.2
  have stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket) := by
    simpa only [frame.values] using readStored
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel uv handle bucket) readAfter true checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  obtain ⟨value, decoded, boundary⟩ := repeated_native_boundary caller.checked.native.machine.heap
    workFuel uv handle bucket readAfter checked checkSuccess
  have created := checkRepeated_created_isolated caller.checked.native.machine.heap workFuel uv handle bucket
    readAfter checked readReady
    (EnumerationPendingReplacement.frame_incoming uv before.core readAfter frame incoming) checkSuccess
  have parkedIsolated : IsolatedPending uv handle parked.core := by
    rw [coreSame]
    exact created
  have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
      [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
  have actual := rows
  rw [← coreSame] at actual
  change (if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
      else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), parked.core)]) =
      [Except.ok ((updated, next), core)] at actual
  split at actual
  · cases actual
  · have fields : metadata = updated ∧
        SourcePruningEnumerationRestart.decision stop order metadata parked = next ∧ parked.core = core := by
      simpa only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, and_true, and_assoc] using actual
    have framed : EnumerationExpandableIndex.frame core parked = parked := by
      rw [← fields.2.2]
      cases parked
      rfl
    have tailNext : next = SourcePruningEnumerationRestart.decision stop order updated
        (EnumerationExpandableIndex.frame core parked) := by
      rw [← fields.1, framed]
      exact fields.2.1.symm
    have tailIsolated : IsolatedPending uv handle (EnumerationExpandableIndex.frame core parked).core := by
      rw [framed]
      exact parkedIsolated
    obtain ⟨retained, finalDecoded⟩ := tail.isolated_boundary uv handle value tailNext tailIsolated decoded boundary
    exact ⟨handle, bucket, value, stored, decoded, boundary, parkedIsolated, retained,
      finalDecoded, retained.not_discharged⟩
