import MicroCFTA.SourceSynthesisProgramRolesCompression
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap
import MicroCFTA.SourcePruningEnumerationAction

/-!
# Program roles at actual selected-prefix writes

The native producer runs once. Its complete receipt keeps the same endpoints.
Filtering retains complete source rows. A recursive clear cannot target a
marked Program root. These laws do not establish whole traversal preservation.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (SlotRole ProgramSlots)
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "prepare" => SourcePruningEnumerationAction.prepare
variable {Typing Key : Type} {valid : Constraint → Prop} {literal : String → Symbol}
variable [DecidableEq (EdgeKey Symbol Constraint)]

local instance selectedPrefixMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem narrowed_fields
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node) (heap after : NativeHeap)
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
          (run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).1
          (run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).2 =
            .done result after at actual
        have facts := ready.semantic.1.normal.facts
        have constructed := SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) heap facts
          (fun edge member => resident_edges heap facts.linked _ available.resident edge (List.mem_filter.mp member).1)
          (fun edge member => checked edge (List.mem_filter.mp member).1)
        exact (MergedSourceComparison.Result.done.inj actual).1 ▸ constructed

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem write_slots
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
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

/-- The same native receipt retains Program slots through replacement and recursive clear. -/
theorem selected_prefix_program_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (heap : NativeHeap) (before readAfter entry : Core)
    (readFuel uv oldHandle : Nat) (scs : List Suspended)
    (ready : SourceEqualityRequiredCache.Ready heap) (realized : PendingRealized heap before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (entered : Frame readAfter entry) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked) :
    (∃ (oldValue result : Node) (nativeFuel : Nat) (nextHeap : NativeHeap) (newHandle : Nat),
      lookupNode heap oldHandle = some oldValue ∧ encodeNode oldValue = some oldHandle ∧
      Available heap oldValue ∧ oldValue.free = [] ∧
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap = .done result nextHeap ∧
      (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
        .done result nextHeap) ∧
      SourceEqualityRequiredCache.Keeps heap nextHeap ∧ Available nextHeap result ∧ result.free = [] ∧
      encodeNode result = some newHandle ∧ lookupNode nextHeap newHandle = some result ∧
      lookupNode nextHeap oldHandle = some oldValue ∧
      Frame before readAfter ∧ PendingRealized nextHeap entry ∧
      (EnumerationReferences.PendingReferences before → EnumerationReferences.PendingReferences entry) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before → EnumerationReferences.IncomingAvoid held entry) ∧
      (result ≠ .empty → oldValue ≠ .empty) ∧
      ProgramSlots valid literal nextHeap entry marked ∧
      (result = .empty → ∀ representativeFuel,
        prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
          .done (result, some (reject : EnumerateM Symbol Constraint Unit)) nextHeap ∧
        ¬ ∃ final : Core, Success (reject : EnumerateM Symbol Constraint Unit) entry () final) ∧
      (result ≠ .empty → newHandle = oldHandle →
        result = oldValue ∧
        (∀ representativeFuel,
          prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
            .done (result, some (pure () : EnumerateM Symbol Constraint Unit)) nextHeap) ∧
        Success (pure () : EnumerateM Symbol Constraint Unit) entry () entry) ∧
      (result ≠ .empty → newHandle ≠ oldHandle →
        ∃ (root size rereadFuel : Nat) (rereadAfter final : Core),
          UnionFind.Reaches before.representatives uv root size ∧
          Success (representative rereadFuel uv) entry root rereadAfter ∧
          Frame entry rereadAfter ∧ Frame before rereadAfter ∧
          rereadAfter.values[root]? = some (.unenumerated (some oldHandle) scs) ∧
          root < rereadAfter.values.length ∧ PendingRealized nextHeap rereadAfter ∧
          Success (setValue root (.unenumerated (some newHandle) scs)) rereadAfter () final ∧
          final = {rereadAfter with values := rereadAfter.values.set root (.unenumerated (some newHandle) scs)} ∧
          final.values[root]? = some (.unenumerated (some newHandle) scs) ∧ PendingRealized nextHeap final ∧
          (EnumerationReferences.PendingReferences before → EnumerationReferences.PendingReferences final) ∧
          (∀ held, EnumerationReferences.IncomingAvoid held before → EnumerationReferences.IncomingAvoid held final) ∧
          prepare holeKey fits admits metadata nativeFuel rereadFuel uv oldHandle scs oldValue heap =
            .done (result, some ((representative rereadFuel uv >>= fun selected =>
              setValue selected (.unenumerated (some newHandle) scs)) : EnumerateM Symbol Constraint Unit)) nextHeap ∧
          Success (representative rereadFuel uv >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) scs)) entry () final ∧
          ProgramSlots valid literal nextHeap final marked)) ∧
    (∀ (target handle : Nat) (bucket : List Suspended) (value : Node) (after : Core),
      entry.values[target]? = some (.unenumerated (some handle) bucket) →
      lookupNode heap handle = some value → MergedOrdinaryHeight.recursiveBoundary value = true →
      Success (setValue target (.unenumerated (some handle) [])) entry () after →
      ¬marked target ∧ after = {entry with values := entry.values.set target (.unenumerated (some handle) [])} ∧
      ProgramSlots valid literal heap after marked) := by
  have readFrame : Frame before readAfter := (getValue_frame readFuel uv before readAfter _ total observed).1
  have entrySlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    heap before entry marked (readFrame.trans entered) slots
  constructor
  · obtain ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
      oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
      newEncoded, newDecoded, oldRetained, firstFrame, entryRealized, pendingPass,
      incomingPass, survivingOld, emptyBranch, equalBranch, changedBranch⟩ :=
      SourcePruningEnumerationAction.prepare_pending_complete holeKey fits admits metadata
        heap before readAfter entry readFuel uv oldHandle scs ready realized total observed entered
    have nextSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
      heap nextHeap entry marked kept entrySlots
    refine ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
      oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
      newEncoded, newDecoded, oldRetained, firstFrame, entryRealized, pendingPass,
      incomingPass, survivingOld, nextSlots, emptyBranch, equalBranch, ?_⟩
    intro nonempty different
    obtain ⟨root, size, rereadFuel, rereadAfter, final, rootPath, reread, rereadFrame, wholeFrame,
      oldStored, inside, rereadRealized, written, shape, finalStored, finalRealized,
      finalPending, finalIncoming, prepared, actual⟩ := changedBranch nonempty different
    have rereadSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      nextHeap entry rereadAfter marked rereadFrame nextSlots
    refine ⟨root, size, rereadFuel, rereadAfter, final, rootPath, reread, rereadFrame, wholeFrame,
      oldStored, inside, rereadRealized, written, shape, finalStored, finalRealized,
      finalPending, finalIncoming, prepared, actual, ?_⟩
    apply write_slots nextHeap rereadAfter final marked rereadSlots root
      (.unenumerated (some newHandle) scs) ?_ ?_ written
    · intro held known
      change EnumerationReferences.InputsAllowed
        (fun other => ¬UnionFind.SameClass rereadAfter.representatives held other) scs
      exact rereadSlots.incoming held known (.unenumerated (some oldHandle) scs)
        (List.mem_of_getElem? oldStored)
    · intro known
      obtain ⟨payload, stored, role⟩ := rereadSlots.stored root known
      have same : payload = .unenumerated (some oldHandle) scs := Option.some.inj (stored.symm.trans oldStored)
      subst payload
      cases role with
      | pending handle bucket original decoded fields validTries annotationPaths =>
          have sameValue : original = oldValue := Option.some.inj (decoded.symm.trans oldRetained)
          have originalFields : ValueFields valid literal oldValue := sameValue ▸ fields
          have resultFields := narrowed_fields holeKey fits admits metadata nativeFuel uv oldValue result
            heap nextHeap ready oldAvailable originalFields narrowed
          exact .pending newHandle _ result newDecoded resultFields validTries annotationPaths
  · intro target handle bucket value after stored decoded boundary written
    have unmarked : ¬marked target := by
      intro known
      obtain ⟨payload, present, role⟩ := entrySlots.stored target known
      have same : payload = .unenumerated (some handle) bucket := Option.some.inj (present.symm.trans stored)
      subst payload
      cases role with
      | pending native scs original found fields _validTries _annotationPaths =>
          have sameValue : original = value := Option.some.inj (found.symm.trans decoded)
          have originalFields : ValueFields valid literal value := sameValue ▸ fields
          cases originalFields <;> cases boundary
    refine ⟨unmarked, (EnumerationDriver.modify_success _ entry after).mp written, ?_⟩
    apply write_slots heap entry after marked entrySlots target (.unenumerated (some handle) []) ?_ ?_ written
    · intro held known sc member
      cases member
    · intro impossible
      exact (unmarked impossible).elim

end MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix
