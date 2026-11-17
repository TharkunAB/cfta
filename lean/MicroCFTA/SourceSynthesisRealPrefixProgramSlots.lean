import MicroCFTA.SourcePruningNativeMeaning
import MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix
import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources
import MicroCFTA.SourcePruningNativeContext
import MicroCFTA.MergedFreshOrdinaryColdEffects

namespace MicroCFTA.SourceSynthesisRealPrefixProgramSlots
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots SlotRole)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList
set_option autoImplicit false

/- Note [Actual prefix role transport]
These local primitive proofs reuse checked proof text from
SourceSynthesisProgramRolesSharedDriver. They run the existing operations.
The read, recursion check, native filter and representative fuels are separate.
The public law inspects the literal prefix once and retains each cached
candidate, including candidates whose callback stops or fails.
No PrefixValid, adequate replay, future callback or new runtime is used.
-/

variable {literal : String → Symbol}

private theorem observed_narrow_fields
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node) (heap after : NativeHeap)
    (valid : Constraint → Prop)
    (ready : SourceEqualityRequiredCache.Ready heap) (available : Available heap value)
    (fields : ValueFields valid literal value)
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value heap = .done result after) :
    ValueFields valid literal result := by
  by_cases inside : uv ∈ metadata.types
  · have same := (MergedSourceComparison.Result.done.inj
      ((SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value heap inside).symm.trans actual)).1
    exact same ▸ fields
  · cases fields with
    | empty =>
        have fallback := SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          .empty heap (by intro entry body depth ordinary impossible; cases impossible) inside
        have same := (MergedSourceComparison.Result.done.inj
          ((fallback.trans (SourcePruningEnumerationIdentity.narrowAt_empty fits admits fuel _ heap)).symm.trans actual)).1
        exact same ▸ ValueFields.empty
    | node entry rows depth free checked =>
        rw [SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          (.node entry rows depth free) heap
          (by intro other body nested ordinary impossible; cases impossible) inside] at actual
        change MergedSourceComparison.Result.done
          (InternedConstructorTemplates.run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).1
          (InternedConstructorTemplates.run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).2 =
            .done result after at actual
        have facts := ready.semantic.1.normal.facts
        have constructed := SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) heap facts
          (fun edge member => InternedEdgeResidency.resident_edges heap facts.linked _ available.resident edge (List.mem_filter.mp member).1)
          (fun edge member => checked edge (List.mem_filter.mp member).1)
        exact (MergedSourceComparison.Result.done.inj actual).1 ▸ constructed

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem observed_write_slots
    (valid : Constraint → Prop) (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked) (target : Nat) (payload : UVarValue Symbol)
    (allowed : ∀ uv, marked uv → EnumerationReferences.InputsAllowed
      (fun other => ¬UnionFind.SameClass before.representatives uv other) (references payload))
    (checked : marked target → SlotRole valid literal heap marked payload)
    (written : Success (setValue target payload) before () after) :
    ProgramSlots valid literal heap after marked := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    simpa only [shape] using slots.bounded uv known
  · intro uv known
    simpa only [shape] using slots.roots uv known
  · intro uv known
    have incoming := EnumerationReferences.setValue_allowed
      (fun other => ¬UnionFind.SameClass before.representatives uv other) target payload before after
      (slots.incoming uv known) (allowed uv known) written
    simpa only [EnumerationReferences.IncomingAvoid, shape] using incoming
  · intro uv known
    by_cases same : uv = target
    · subst uv
      obtain ⟨old, stored, _role⟩ := slots.stored target known
      have inside := (List.getElem?_eq_some_iff.mp stored).1
      exact ⟨payload, by simpa only [shape] using (List.getElem?_set_self inside :
        (before.values.set target payload)[target]? = some payload), checked known⟩
    · obtain ⟨old, stored, role⟩ := slots.stored uv known
      exact ⟨old, by simpa only [shape, List.getElem?_set_ne (Ne.symm same)] using stored, role⟩

private theorem observed_narrow_available
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before =
      .done result after) : Available after result ∧ result.free = [] := by
  have skipped (same : result = value ∧ after = before) : Available after result ∧ result.free = [] := by
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨available, closed⟩
  by_cases typed : uv ∈ metadata.types
  · have pureDone := SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed
    have same := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨same.1.symm, same.2.symm⟩
  · cases value with
    | mu =>
        have same := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨same.1.symm, same.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [SourcePruningOuterNarrow.narrow, typed] at narrowed
        obtain ⟨rows, middle, exposed, built, _meaning⟩ := SourcePruningNativeView.narrowAt_edges
          (fun _ _ => true) (fun _ _ => False) fits admits (holeKey metadata.typing uv) fuel _ before
          result after ready available closed narrowed
        have verified := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel _ before
          ready.semantic ready.covered available closed
        have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using verified.semantic
        have resident : InternedNestedProvenance.Edges middle
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.edges rows middle exposed edge (List.mem_filter.mp member).1
        have children : ∀ child ∈ (rows.filter
            (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))).flatMap EdgeValue.children,
            Available middle child := by
          intro child member
          obtain ⟨edge, member, included⟩ := List.mem_flatMap.mp member
          exact semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge member) child included
        have constructed := InternedProbeProvenance.makeNode_available
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts.coherent semantic.1.normal.facts.cached children
        have closedRows : MergedColdReaderClosedInputs.ClosedEdges
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.closed rows middle exposed edge (List.mem_filter.mp member).1
        have constructedClosed := MergedColdReaderClosedInputs.makeNode_closed
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts resident closedRows
        rw [built] at constructed constructedClosed
        exact ⟨constructed.2.2, constructedClosed⟩

private theorem observed_prepared_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (readFuel checkFuel nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : NativeHeap)
    (action : EnumerateM Symbol Constraint Unit) (before readAfter checked after : Core)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (ready : EnumerationDriver.Ready uv before)
    (nativeReady : SourceEqualityRequiredCache.Ready heap)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap before)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap)
    (decoded : lookupNode heap oldHandle = some oldValue)
    (reading : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter false checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (executed : Success action checked () after) :
    ProgramSlots valid literal nextHeap after marked := by
  obtain ⟨readFrame, root, size, oldPath, _readPath, oldStored⟩ :=
    getValue_frame readFuel uv before readAfter _ ready.safe.1.total reading
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap checkFuel uv oldHandle scs
    readAfter checked (readFrame.total ready.safe.1.total) checking
  have checkedFrame := readFrame.trans checkFrame
  have nativeSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots heap nextHeap before marked kept slots
  have checkedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    nextHeap before checked marked checkedFrame nativeSlots
  have selectedAction := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at selectedAction
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected => setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj selectedAction).1).2
  rw [actionSame] at executed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at executed
    obtain ⟨_unit, afterSame⟩ := (success_pure () () checked after).mp executed
    simpa only [afterSame] using checkedSlots
  · rw [ite_eq_right same] at executed
    obtain ⟨selected, resolved, resolution, writing⟩ := (success_bind _ _ _ _ _).mp executed
    have resolvedFrame := representative_frame representativeFuel uv selected checked resolved
      (checkedFrame.total ready.safe.1.total) resolution
    have wholeFrame := checkedFrame.trans resolvedFrame
    obtain ⟨found, lookup, selectedSame, _resolvedSame⟩ :=
      (representative_success representativeFuel uv checked resolved selected).mp resolution
    have path := (UnionFind.findRoot_correct representativeFuel checked.representatives uv found lookup).1
    have rootSame : selected = root := selectedSame.trans
      (UnionFind.reaches_unique path ((checkedFrame.reaches uv root size).mpr oldPath)).1
    have stored : resolved.values[selected]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [wholeFrame.values, rootSame] using oldStored
    have resolvedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      nextHeap checked resolved marked resolvedFrame checkedSlots
    apply observed_write_slots valid nextHeap resolved after marked resolvedSlots selected
      (.unenumerated (some newHandle) scs) ?_ ?_ writing
    · intro held tagged
      change EnumerationReferences.InputsAllowed
        (fun other => ¬UnionFind.SameClass resolved.representatives held other) scs
      exact resolvedSlots.incoming held tagged (.unenumerated (some oldHandle) scs)
        (List.mem_of_getElem? stored)
    · intro tagged
      have oldStoredAtUv : before.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
        have actualStored := (EnumerationDriver.getValue_root readFuel uv before readAfter _
          ready.safe ready.inside ready.root reading).2.2.2
        simpa only [readFrame.values] using actualStored
      obtain ⟨original, originalDecoded, oldAvailable, oldClosed⟩ := realized uv oldHandle scs oldStoredAtUv
      have originalSame : original = oldValue := Option.some.inj (originalDecoded.symm.trans decoded)
      subst original
      obtain ⟨payload, present, role⟩ := resolvedSlots.stored selected tagged
      have payloadSame : payload = .unenumerated (some oldHandle) scs :=
        Option.some.inj (present.symm.trans stored)
      subst payload
      cases role with
      | pending handle bucket source found fields validTries annotationPaths =>
          have retained := lookupNode_keeps heap nextHeap kept oldHandle oldValue decoded
          have sourceSame : source = oldValue := Option.some.inj (found.symm.trans retained)
          have oldFields : ValueFields valid literal oldValue := sourceSame ▸ fields
          have newFields := observed_narrow_fields holeKey fits admits metadata nativeFuel uv oldValue value heap nextHeap
            valid nativeReady oldAvailable oldFields narrowed
          have resultAvailable := observed_narrow_available holeKey fits admits metadata nativeFuel uv oldValue value
            heap nextHeap nativeReady oldAvailable oldClosed narrowed
          obtain ⟨actualHandle, actualEncoded, actualDecoded⟩ := available_readback nextHeap value
            kept.ready.semantic.1.normal.facts.coherent resultAvailable.1 resultAvailable.2
          have handleSame : actualHandle = newHandle := Option.some.inj (actualEncoded.symm.trans encoded)
          subst actualHandle
          exact .pending newHandle scs value actualDecoded newFields validTries annotationPaths

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem observed_repeated_slots
    (heap : NativeHeap) (readFuel checkFuel uv handle : Nat) (scs : List Suspended)
    (before readAfter checked : Core) (safe : Safe before)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (reading : Success (getValue readFuel uv) before (.unenumerated (some handle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle scs)
      readAfter true checked) : ProgramSlots valid literal heap checked marked := by
  obtain ⟨readFrame, oldRoot, size, oldPath, _readPath, oldStored⟩ :=
    getValue_frame readFuel uv before readAfter _ safe.1.total reading
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) readAfter true checked := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using checking
      exact (success_failure .unresolvedReference readAfter checked true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at checking
        obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp checking
        have resolvedFrame := representative_frame checkFuel uv selected readAfter resolved
          (readFrame.total safe.1.total) resolution
        have wholeFrame := readFrame.trans resolvedFrame
        obtain ⟨found, lookup, selectedSame, _resolvedSame⟩ :=
          (representative_success checkFuel uv readAfter resolved selected).mp resolution
        have path := (UnionFind.findRoot_correct checkFuel readAfter.representatives uv found lookup).1
        have rootSame : selected = oldRoot := selectedSame.trans
          (UnionFind.reaches_unique path ((readFrame.reaches uv oldRoot size).mpr oldPath)).1
        have stored : resolved.values[selected]? = some (.unenumerated (some handle) scs) := by
          simpa only [wholeFrame.values, rootSame] using oldStored
        have resolvedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
          heap before resolved marked wholeFrame slots
        obtain ⟨current, currentState, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp read
        subst current
        subst currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry selected
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_answer, afterSame⟩ := (success_pure true true written checked).mp finished
          rw [afterSame]
          apply observed_write_slots valid heap resolved written marked resolvedSlots selected
            (.unenumerated (some handle) []) ?_ ?_ writing
          · intro held tagged sc member
            cases member
          · intro tagged
            obtain ⟨payload, present, role⟩ := resolvedSlots.stored selected tagged
            have payloadSame : payload = .unenumerated (some handle) scs :=
              Option.some.inj (present.symm.trans stored)
            subst payload
            cases role with
            | pending native bucket original found fields _validTries _annotationPaths =>
                have same : original = value := Option.some.inj (found.symm.trans decoded)
                have valueFields : ValueFields valid literal value := same ▸ fields
                cases valueFields <;> cases boundary
        · rw [ite_eq_right seen] at continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved checked).mp continued
          cases impossible
      · have impossible : Success (pure false : EnumerateM Symbol Constraint Bool) readAfter true checked := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using checking
        obtain ⟨contradiction, _same⟩ := (success_pure false true readAfter checked).mp impossible
        cases contradiction

/-- Every cached candidate of the actual real prefix retains all PAST Program slots. -/
theorem runPrefix_program_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before memos.query with
    | .parked _ (some after) _ =>
        ProgramSlots valid literal caller.checked.native.machine.heap after.core marked
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        ProgramSlots valid literal reached.checked.native.machine.heap after.core marked
    | _ => True
 := by
  classical
  obtain ⟨ready, _incoming, _selectedPayload⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readSuccess : Success (getValue readFuel uv) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    by_cases checkedResult : ∃ (repeated : Bool) (checked : Core),
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = [.ok (repeated, checked)]
    · obtain ⟨repeated, checked, checking⟩ := checkedResult
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs) readAfter repeated checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      cases repeated with
      | true =>
          have checkedSlots := observed_repeated_slots caller.checked.native.machine.heap
            readFuel checkFuel uv oldHandle scs before.core readAfter checked packet.safe
            valid marked slots readSuccess checkSuccess
          unfold SourcePruningEnumerationSelectedStep.runPrefix
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          simp only [reading, checking]
          cases adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
              indexFuel uv oldHandle scs before checked with
          | none => trivial
          | some attached =>
              change ProgramSlots valid literal caller.checked.native.machine.heap attached.core marked
              rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
                indexFuel uv oldHandle scs before attached checked adapted]
              exact checkedSlots
      | false =>
          cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
          | none =>
              simp only [SourcePruningEnumerationSelectedStep.runPrefix,
                SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, oldDecoded]
          | some oldValue =>
              have readStored := (EnumerationDriver.getValue_root readFuel uv before.core readAfter
                (.unenumerated (some oldHandle) scs) packet.safe ready.inside ready.root readSuccess).2.2.2
              have readFrame := (getValue_frame readFuel uv before.core readAfter
                (.unenumerated (some oldHandle) scs) packet.safe.1.total readSuccess).1
              have originalStored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
                simpa only [readFrame.values] using readStored
              obtain ⟨original, originalDecoded, oldAvailable, oldClosed⟩ :=
                realized uv oldHandle scs originalStored
              have originalSame : original = oldValue := Option.some.inj (originalDecoded.symm.trans oldDecoded)
              subst original
              unfold SourcePruningEnumerationSelectedStep.runPrefix
                SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              simp only [reading, checking, oldDecoded,
                ← SourcePruningEnumerationAction.prepare_configured_eq]
              cases preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
                  holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue
                  caller.checked.native.machine.heap with
              | failed fault heap => trivial
              | done pair heap =>
                  obtain ⟨value, possibleAction⟩ := pair
                  cases possibleAction with
                  | none => trivial
                  | some action =>
                      dsimp only
                      by_cases ran : ∃ observed : Core,
                          ExceptT.run (action checked) = [.ok ((), observed)]
                      · obtain ⟨observed, raw⟩ := ran
                        have actionSuccess : Success action checked () observed := by
                          rw [Success, raw]
                          exact List.mem_singleton_self _
                        simp only [raw]
                        cases encoded : encodeNode value with
                        | none => trivial
                        | some newHandle =>
                            dsimp only
                            cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                                uv oldHandle newHandle scs before observed with
                            | none => trivial
                            | some attached =>
                                dsimp only
                                have narrowed := SourcePruningEnumerationSharedRecursive.prepared_done_narrowed
                                  holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs
                                  oldValue value caller.checked.native.machine.heap heap action preparedEq
                                have nonempty := SourcePruningEnumerationSharedRecursive.prepared_success_nonempty
                                  holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs
                                  oldValue value caller.checked.native.machine.heap heap action checked observed
                                  preparedEq raw
                                obtain ⟨final, post, _unfolding, _querySame⟩ := SourcePruningNativeContext.outer_post
                                  formulas solver inventory caller memos holeKey fits admits metadata nativeFuel uv
                                  oldValue value heap packet.context oldAvailable narrowed
                                have kept : SourceEqualityRequiredCache.Keeps
                                    caller.checked.native.machine.heap heap := post.effects.keeps
                                have observedSlots := observed_prepared_slots holeKey fits admits metadata
                                  readFuel checkFuel nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value
                                  caller.checked.native.machine.heap heap action before.core readAfter checked observed
                                  valid marked slots ready packet.context.ready.semantic.ready realized kept oldDecoded
                                  readSuccess checkSuccess narrowed nonempty encoded preparedEq actionSuccess
                                have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core heap indexFuel
                                  uv oldHandle newHandle scs before attached observed adapted
                                have attachedSlots : ProgramSlots valid literal heap attached.core marked := by
                                  rw [attachedCore]
                                  exact observedSlots
                                have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                    graph templates callbackFuel metadata uv (.inr newHandle) attached.core) =
                                    [.ok ((false, metadata), attached.core)] := by
                                  rw [SourcePruningRecordTypes.recordTypes_inr]
                                  rfl
                                simp only [recorded]
                                exact attachedSlots
                      · generalize rawEq : ExceptT.run (action checked) = rawAction
                        cases rawAction with
                        | nil => trivial
                        | cons first rest =>
                            cases first with
                            | error fault => trivial
                            | ok pair =>
                                obtain ⟨token, observed⟩ := pair
                                cases token
                                cases rest with
                                | nil => exact (ran ⟨observed, rawEq⟩).elim
                                | cons another remaining => trivial
    · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before memos.query =
          .stopped (ExceptT.run (getValue readFuel uv before.core))
            (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter))) := by
        unfold SourcePruningEnumerationSelectedStep.runPrefix
          SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        simp only [reading]
        split
        · exact (checkedResult ⟨true, _, by assumption⟩).elim
        · exact (checkedResult ⟨false, _, by assumption⟩).elim
        · rfl
      simp only [stopped]
  · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before memos.query =
        .stopped (ExceptT.run (getValue readFuel uv before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix
        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    simp only [stopped]

end MicroCFTA.SourceSynthesisRealPrefixProgramSlots
