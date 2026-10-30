import MicroCFTA.SourcePruningNarrowReturnedControl
import MicroCFTA.SourcePruningEnumerationRecursion
import MicroCFTA.EnumerationObservations

/-!
# Actual changed-filter slot transport

The actual false recursion check preserves the complete slot frame.
A successful changed preparation action then writes its actual normal result
into the same allocated representative slot. Other writers need separate laws.

-/
namespace MicroCFTA.SourcePruningEnumerationRecursion
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance slotCheckMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- An actual false recursion check preserves slots, ancestry, and representative classes. -/
theorem checkRepeated_false_frame
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (checkRepeated heap fuel uv handle scs) before false after) :
    Frame before after := by
  cases decoded : SourcePruningEnumerationNodes.lookupNode heap handle with
  | none =>
      simp only [checkRepeated, decoded] at observed
      exact False.elim (success_failure .unresolvedReference before after false observed)
  | some value =>
      simp only [checkRepeated, decoded] at observed
      split at observed
      · obtain ⟨root, middle, reading, continued⟩ := (success_bind _ _ before false after).mp observed
        obtain ⟨current, next, getting, finished⟩ := (success_bind _ _ middle false after).mp continued
        obtain ⟨sameCurrent, sameNext⟩ := (EnumerationDriver.get_success middle next current).mp getting
        rw [sameCurrent, sameNext] at finished
        split at finished
        · obtain ⟨_unit, written, writing, impossible⟩ := (success_bind _ _ middle false after).mp finished
          have contradiction := ((success_pure true false written after).mp impossible).1
          cases contradiction
        · exact (representative_frame fuel uv root before middle total reading).trans
            (pure_frame false false middle after finished)
      · exact pure_frame false false before after observed

end MicroCFTA.SourcePruningEnumerationRecursion

namespace MicroCFTA.SourcePruningEnumerationAction
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationObservations
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourcePruningNativeView SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {EnumGuard NativeGuard Typing Key : Type}

local instance slotTransportMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Actual read, false check, preparation, and action success store the returned physical normal form. -/
theorem prepare_changed_success_stores_normal [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel uv oldHandle newHandle : Nat)
    (scs : List Suspended) (value result : Value Symbol NativeGuard)
    (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before readAfter checked final : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard Unit)
    (ready : SourceEqualityRequiredCache.Ready heap) (realized : PendingRealized heap before)
    (total : UnionFind.Total before.representatives)
    (read : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (checkedFalse : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter false checked)
    (decoded : lookupNode heap oldHandle = some value)
    (prepared : prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs value heap =
      .done (result, some action) nextHeap)
    (newEncoded : encodeNode result = some newHandle) (changed : newHandle ≠ oldHandle)
    (succeeded : Success action checked () final) :
    SourceEqualityRequiredCache.Keeps heap nextHeap ∧
      Available nextHeap result ∧ result.free = [] ∧ SourceEqualityRequiredCache.Ordinary result ∧
      EqualityOrdinaryReadback.Normal nextHeap result ∧ lookupNode nextHeap newHandle = some result ∧
      (∀ edge ∈ nodeEdges result, keeps fits admits (holeKey metadata.typing uv) edge = true) ∧
      (SourceEqualityRequiredCache.Ordinary value → ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value) ∧
      PendingRealized nextHeap final ∧
      ∃ (root : Nat) (middle : EnumerationState.State Symbol EnumGuard),
        Success (representative representativeFuel uv) checked root middle ∧ Frame checked middle ∧
        middle.values[root]? = some (.unenumerated (some oldHandle) scs) ∧
        Success (setValue root (.unenumerated (some newHandle) scs)) middle () final ∧
        final = {middle with values := middle.values.set root (.unenumerated (some newHandle) scs)} ∧
        final.values[root]? = some (.unenumerated (some newHandle) scs) := by
  obtain ⟨found, readLookup, oldStored, readState⟩ :=
    (getValue_success readFuel uv before readAfter (.unenumerated (some oldHandle) scs)).mp read
  obtain ⟨oldValue, oldDecoded, oldAvailable, oldClosed⟩ :=
    realized found.representative oldHandle scs oldStored
  have sameOld : oldValue = value := Option.some.inj (oldDecoded.symm.trans decoded)
  subst oldValue
  have oldEncoded := SourcePruningEnumerationIdentity.lookup_encode heap oldHandle value
    ready.semantic.1.normal.facts.coherent decoded
  obtain ⟨filtered, kept, resultAvailable, resultClosed, resultOrdinary, resultNormal, resultKept, _replay⟩ :=
    prepare_changed_returned_control holeKey fits admits metadata nativeFuel representativeFuel uv
      oldHandle newHandle scs value result heap nextHeap (some action) ready oldAvailable oldClosed
      prepared oldEncoded newEncoded changed
  have actionShape : action = (representative representativeFuel uv >>= fun selected =>
      setValue selected (.unenumerated (some newHandle) scs)) := by
    cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value heap with
    | failed =>
        simp only [prepare, narrowed] at prepared
        cases prepared
    | done candidate reached =>
        simp only [prepare, narrowed] at prepared
        have paired := MergedSourceComparison.Result.done.inj prepared
        have sameValue : candidate = result := congrArg Prod.fst paired.1
        subst candidate
        have sameAction := congrArg Prod.snd paired.1
        cases result with
        | empty =>
            have rejected : action = (reject : EnumerateM Symbol EnumGuard Unit) := (Option.some.inj sameAction).symm
            rw [rejected] at succeeded
            simp [Success, reject, ExceptT.run] at succeeded
        | node entry edges depth free =>
            have same : some (representative representativeFuel uv >>= fun selected =>
                setValue selected (.unenumerated (some newHandle) scs)) = some action := by
              simpa only [newEncoded, ite_eq_right changed] using sameAction
            exact (Option.some.inj same).symm
        | reference | union | mu => cases resultOrdinary
  rw [actionShape] at succeeded
  obtain ⟨root, middle, reread, written⟩ := (success_bind _ _ checked () final).mp succeeded
  have firstRead : Success (representative readFuel uv) before found.representative readAfter :=
    (EnumerationSchedule.representative_success readFuel uv before readAfter found.representative).mpr
      ⟨found, readLookup, rfl, readState⟩
  have firstFrame : Frame before readAfter :=
    representative_frame readFuel uv found.representative before readAfter total firstRead
  have checkFrame := SourcePruningEnumerationRecursion.checkRepeated_false_frame heap checkFuel uv oldHandle scs
    readAfter checked (firstFrame.total total) checkedFalse
  have rereadFrame : Frame checked middle := representative_frame representativeFuel uv root checked middle
    ((firstFrame.trans checkFrame).total total) reread
  have wholeFrame := (firstFrame.trans checkFrame).trans rereadFrame
  have sameRoot := (representative_agrees readFuel representativeFuel uv before checked readAfter middle
    found.representative root (firstFrame.trans checkFrame) total firstRead reread).1
  have middleStored : middle.values[root]? = some (.unenumerated (some oldHandle) scs) := by
    have retained : middle.values[found.representative]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [wholeFrame.values] using oldStored
    simpa only [sameRoot] using retained
  have inside : root < middle.values.length :=
    (List.getElem?_eq_some_iff.mp middleStored).elim (fun bound _ => bound)
  have finalShape : final = {middle with values := middle.values.set root (.unenumerated (some newHandle) scs)} :=
    (EnumerationDriver.modify_success
      (fun state => {state with values := state.values.set root (.unenumerated (some newHandle) scs)}) middle final).mp written
  have finalStored : final.values[root]? = some (.unenumerated (some newHandle) scs) := by
    rw [finalShape]
    exact List.getElem?_set_self inside
  obtain ⟨encodedHandle, encodedResult, decodedResult⟩ := available_readback nextHeap result
    kept.ready.semantic.1.normal.facts.coherent resultAvailable resultClosed
  have sameEncoded : encodedHandle = newHandle := Option.some.inj (encodedResult.symm.trans newEncoded)
  subst encodedHandle
  have middleRealized : PendingRealized nextHeap middle :=
    realized_preserved heap nextHeap before middle realized wholeFrame kept
  obtain ⟨storedHandle, expectedFinal, expectedEncoded, _expectedWrite, expectedShape, _expectedStored, expectedRealized⟩ :=
    SourcePruningEnumerationWrites.write_available_realized nextHeap middle result root scs
      kept.ready.semantic.1.normal.facts.coherent resultAvailable resultClosed middleRealized inside
  have storedSame : storedHandle = newHandle := Option.some.inj (expectedEncoded.symm.trans newEncoded)
  subst storedHandle
  have sameFinal : expectedFinal = final := expectedShape.trans finalShape.symm
  have finalRealized : PendingRealized nextHeap final := by simpa only [sameFinal] using expectedRealized
  have rows : SourceEqualityRequiredCache.Ordinary value →
      ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value := by
    intro ordinary edge member
    exact (narrowAt_ordinary_rows fits admits nativeFuel (holeKey metadata.typing uv) value result heap nextHeap
      ready oldAvailable ordinary filtered edge member).1
  exact ⟨kept, resultAvailable, resultClosed, resultOrdinary, resultNormal, decodedResult, resultKept,
    rows, finalRealized, root, middle, reread, rereadFrame, middleStored, written, finalShape, finalStored⟩

end MicroCFTA.SourcePruningEnumerationAction
