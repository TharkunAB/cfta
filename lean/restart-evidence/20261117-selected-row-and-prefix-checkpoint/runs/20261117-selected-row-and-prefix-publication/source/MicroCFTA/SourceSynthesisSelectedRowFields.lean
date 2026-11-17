import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourceSynthesisAnnotationFieldConstructors
import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources

namespace MicroCFTA.SourceSynthesisSelectedRowFields
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
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
set_option autoImplicit false

/- Note [Fields at the actual real prefix]
The old marked-preparation observer already covers SelectedPreparation.run.
The real prefix first runs OuterNarrow. Its actual singleton receipt fixes
that call and its six original fuels. The marked root supplies the decoded
Program fields. The native filter preserves each complete source row.
The local narrow_fields proof reuses the checked proof text from
SourceSynthesisProgramRolesSelectedPrefix.narrowed_fields. It does not call
that private declaration across modules or substitute an adequate run.
-/

private theorem narrow_fields
    (valid : Constraint → Prop) (literal : String → Symbol)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node) (heap after : NativeHeap)
    (ready : SourceEqualityRequiredCache.Ready heap) (available : Available heap value)
    (fields : ValueFields valid literal value)
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value heap =
      .done result after) : ValueFields valid literal result := by
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
          (fun edge member => InternedEdgeResidency.resident_edges heap facts.linked _ available.resident
            edge (List.mem_filter.mp member).1)
          (fun edge member => checked edge (List.mem_filter.mp member).1)
        exact (MergedSourceComparison.Result.done.inj actual).1 ▸ constructed

/-- A literal successful real prefix derives fields for its exact selected Program row. -/
theorem narrowed_marked_row_fields
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (caller reached : Caller width) (memos : Memos) (before after : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (heap : NativeHeap)
    (action : EnumerateM Symbol Constraint Unit) (checked actionCore callbackCore : Core)
    (received : SourceEndpointMemo.Memos)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before memos.query =
        .narrowed checked (.done (.node entry rows depth free, some action) heap) reached received
          (some [.ok ((), actionCore)]) (some after)
          (some [.ok ((false, updated), callbackCore)]) none)
    (tagged : marked uv) (row : EdgeValue Symbol Constraint) (selected : row ∈ rows) :
    EdgeFields valid literal row
 := by
  obtain ⟨ready, _incoming, _selectedPayload⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  obtain ⟨oldHandle, _newHandle, scs, oldValue, readAfter, reading, _checking,
      decoded, prepared, _encoded, _executed, _adapted, _coreSame, _callbackSame,
      _updatedSame, _reachedSame, _querySame⟩ :=
    SourcePruningEnumerationSharedRecursive.observed_success_stages holeKey fits admits graph templates
      stop order metadata updated readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv
      caller reached before after memos.query received checked actionCore callbackCore
      (.node entry rows depth free) heap action actual
  have readSuccess : Success (getValue readFuel uv) before.core
      (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  obtain ⟨_readSafe, _readCounter, keptRoot, readStored⟩ := EnumerationDriver.getValue_root
    readFuel uv before.core readAfter (.unenumerated (some oldHandle) scs)
    packet.safe ready.inside ready.root readSuccess
  have originalStored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) :=
    keptRoot.value.symm.trans readStored
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨original, originalDecoded, originalAvailable, _originalClosed⟩ :=
    realized uv oldHandle scs originalStored
  have availableSame : original = oldValue := Option.some.inj (originalDecoded.symm.trans decoded)
  have oldAvailable : Available caller.checked.native.machine.heap oldValue :=
    availableSame ▸ originalAvailable
  have oldFields : ValueFields valid literal oldValue := by
    obtain ⟨payload, present, role⟩ := slots.stored uv tagged
    have same : payload = .unenumerated (some oldHandle) scs :=
      Option.some.inj (present.symm.trans originalStored)
    subst payload
    cases role with
    | pending handle bucket original found fields validTries annotationPaths =>
        have sameValue : original = oldValue := Option.some.inj (found.symm.trans decoded)
        exact sameValue ▸ fields
  have narrowed := SourcePruningEnumerationSharedRecursive.prepared_done_narrowed
    holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue
    (.node entry rows depth free) caller.checked.native.machine.heap heap action prepared
  have preparedFields := narrow_fields valid literal holeKey fits admits metadata nativeFuel uv oldValue
    (.node entry rows depth free) caller.checked.native.machine.heap heap
    packet.context.ready.semantic.ready oldAvailable oldFields narrowed
  cases preparedFields with
  | node _ _ _ _ checkedRows => exact checkedRows row selected

end MicroCFTA.SourceSynthesisSelectedRowFields

#check @MicroCFTA.SourceSynthesisSelectedRowFields.narrow_fields
#print axioms MicroCFTA.SourceSynthesisSelectedRowFields.narrow_fields
#check @MicroCFTA.SourceSynthesisSelectedRowFields.narrowed_marked_row_fields
#print axioms MicroCFTA.SourceSynthesisSelectedRowFields.narrowed_marked_row_fields
