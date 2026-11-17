import MicroCFTA.SourcePruningEnumerationSelectedPrefixCanonical
import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion
import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationEntryCanonical

namespace MicroCFTA.SourcePruningEnumerationObservedEntryCanonical
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSelectedStep (runPrefix runPrefixWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/- Note [Canonicality at actual prefix and entry receipts]
The initial canonicality fact concerns stored tries before execution.
The proof follows the actual read, check and action at their supplied fuels.
Both adapters retain the exact observed core. Right recording is pure.
The preparation result then fixes its actual entry bucket.
No sufficient-bound execution or future history is used.
Packet safety supplies Total separately; Packet does not include Canonical.
-/

private theorem prepared_action_canonical
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (canonical : Canonical checked) (valid : ValidSuspended scs)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (actual : Success action checked () after) : Canonical after := by
  have selectedPrepared := prepared
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | failed fault current =>
      simp only [SourcePruningEnumerationAction.prepare,
        SourcePruningEnumerationAction.prepareWithNarrow, narrowed] at prepared
      cases prepared
  | done actualValue current =>
      simp only [SourcePruningEnumerationAction.prepare,
        SourcePruningEnumerationAction.prepareWithNarrow, narrowed] at prepared
      have valueSame : actualValue = value :=
        congrArg Prod.fst (MergedSourceComparison.Result.done.inj prepared).1
      have heapSame : current = nextHeap := (MergedSourceComparison.Result.done.inj prepared).2
      rw [valueSame] at prepared
      have nonempty : value ≠ .empty := by
        intro empty
        have actionField := congrArg Prod.snd (MergedSourceComparison.Result.done.inj prepared).1
        have actionSame : (reject : EnumerateM Symbol Constraint Unit) = action :=
          Option.some.inj (by simpa only [empty] using actionField)
        have impossible : Success (reject : EnumerateM Symbol Constraint Unit) checked () after := by
          rw [actionSame]
          exact actual
        exact EnumerationSchedule.reject_unsuccessful checked after () impossible
      have encoded : ∃ newHandle, encodeNode value = some newHandle := by
        cases value with
        | empty => exact (nonempty rfl).elim
        | reference name =>
            have actionField := congrArg Prod.snd (MergedSourceComparison.Result.done.inj prepared).1
            have impossible : (none : Option (EnumerateM Symbol Constraint Unit)) = some action := by
              simpa only [encodeNode] using actionField
            cases impossible
        | node entry rows depth free => exact ⟨entry.identity + 1, rfl⟩
        | union entry members depth free => exact ⟨entry.identity + 1, rfl⟩
        | mu entry body depth ordinary => exact ⟨entry.identity + 1, rfl⟩
      obtain ⟨newHandle, encoded⟩ := encoded
      have actualNarrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
          .done value nextHeap := by
        simpa only [valueSame, heapSame] using narrowed
      exact SourcePruningEnumerationSelectedPrefixCanonical.prepared_nonempty_canonical
        holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value
        heap nextHeap action checked after canonical valid actualNarrowed nonempty encoded selectedPrepared actual

theorem runPrefix_canonical
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (canonical : Canonical before.core) :
    match runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries with
    | .stopped _ _ => True
    | .parked checked candidate _ =>
        Canonical checked ∧ ∀ after, candidate = some after → Canonical after.core
    | .narrowed checked _ _ _ _ candidate _ _ =>
        Canonical checked ∧ ∀ after, candidate = some after → Canonical after.core
 := by
  classical
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readSuccess : Success (getValue readFuel uv) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have readFacts := getValue_canonical readFuel uv before.core readAfter
      (.unenumerated (some oldHandle) scs) canonical readSuccess
    by_cases checkedResult : ∃ (repeated : Bool) (checked : Core),
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = [.ok (repeated, checked)]
    · obtain ⟨repeated, checked, checking⟩ := checkedResult
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs) readAfter repeated checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have checkedCanonical := SourcePruningEnumerationSelectedPrefixCanonical.checkRepeated_canonical
        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter checked repeated
        readFacts.1 checkSuccess
      cases repeated with
      | true =>
          unfold runPrefix runPrefixWithNarrow
          simp only [reading, checking]
          refine ⟨checkedCanonical, ?_⟩
          intro after adapted
          rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
            indexFuel uv oldHandle scs before after checked adapted]
          exact checkedCanonical
      | false =>
          have noCandidate : Canonical checked ∧
              ∀ after, (none : Option Cached) = some after → Canonical after.core := by
            refine ⟨checkedCanonical, ?_⟩
            intro after impossible
            cases impossible
          cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
          | none =>
              simp only [runPrefix, runPrefixWithNarrow, reading, checking, oldDecoded]
          | some oldValue =>
              unfold runPrefix runPrefixWithNarrow
              simp only [reading, checking, oldDecoded,
                ← SourcePruningEnumerationAction.prepare_configured_eq]
              cases preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
                  nativeFuel representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap with
              | failed fault heap =>
                  exact noCandidate
              | done pair heap =>
                  obtain ⟨narrowedValue, possibleAction⟩ := pair
                  cases possibleAction with
                  | none =>
                      exact noCandidate
                  | some action =>
                      dsimp only
                      by_cases ran : ∃ observed : Core,
                          ExceptT.run (action checked) = [.ok ((), observed)]
                      · obtain ⟨observed, raw⟩ := ran
                        have actionSuccess : Success action checked () observed := by
                          rw [Success, raw]
                          exact List.mem_singleton_self _
                        have observedCanonical := prepared_action_canonical holeKey fits admits metadata
                          nativeFuel representativeFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed checkedCanonical
                          readFacts.2 preparedEq actionSuccess
                        simp only [raw]
                        cases encoded : encodeNode narrowedValue with
                        | none =>
                            exact noCandidate
                        | some newHandle =>
                            dsimp only
                            cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                                uv oldHandle newHandle scs before observed with
                            | none =>
                                exact noCandidate
                            | some attached =>
                                dsimp only
                                have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core heap
                                  indexFuel uv oldHandle newHandle scs before attached observed adapted
                                have attachedCanonical : Canonical attached.core := by
                                  rw [attachedCore]
                                  exact observedCanonical
                                have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                    graph templates callbackFuel metadata uv (.inr newHandle) attached.core) =
                                    [.ok ((false, metadata), attached.core)] := by
                                  rw [SourcePruningRecordTypes.recordTypes_inr]
                                  rfl
                                simp only [recorded]
                                refine ⟨checkedCanonical, ?_⟩
                                intro after candidate
                                cases candidate
                                exact attachedCanonical
                      · generalize rawEq : ExceptT.run (action checked) = rawAction
                        cases rawAction with
                        | nil => exact noCandidate
                        | cons first rest =>
                            cases first with
                            | error fault => exact noCandidate
                            | ok pair =>
                                obtain ⟨token, observed⟩ := pair
                                cases token
                                cases rest with
                                | nil => exact (ran ⟨observed, rawEq⟩).elim
                                | cons another remaining => exact noCandidate
    · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
          readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
          .stopped (ExceptT.run (getValue readFuel uv before.core))
            (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter))) := by
        unfold runPrefix runPrefixWithNarrow
        simp only [reading]
        split
        · exact (checkedResult ⟨true, _, by assumption⟩).elim
        · exact (checkedResult ⟨false, _, by assumption⟩).elim
        · rfl
      simp only [stopped]
  · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
        .stopped (ExceptT.run (getValue readFuel uv before.core)) none := by
      unfold runPrefix runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    simp only [stopped]


theorem successful_preparation_bucket_valid
    (entryFuel nativeFuel uv target handle : Nat) (bucket : List Suspended)
    (caller : Caller width) (before : Cached) (entered : Core) (decoded result : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (canonical : Canonical before.core)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, bucket, decoded), entered)], some (.done result heap))) :
    Canonical entered ∧ ValidSuspended bucket
 := by
  have reading := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    entryFuel uv before.core) = [.ok ((target, handle, bucket, decoded), entered)] at reading
  have successful : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      entryFuel uv) before.core (target, handle, bucket, decoded) entered := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  exact SourcePruningEnumerationEntry.enter_canonical caller.checked.native.machine.heap
    entryFuel uv before.core entered target handle bucket decoded canonical successful

end MicroCFTA.SourcePruningEnumerationObservedEntryCanonical
