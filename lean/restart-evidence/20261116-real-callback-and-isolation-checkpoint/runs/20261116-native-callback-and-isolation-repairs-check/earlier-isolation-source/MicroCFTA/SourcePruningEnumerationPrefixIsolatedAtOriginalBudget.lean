import MicroCFTA.SourcePruningEnumerationPrefixIsolatedHistory

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates EnumerationDischargeHistory
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem prepared_action_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing)
    (held heldHandle nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (isolated : IsolatedPending held heldHandle checked)
    (total : UnionFind.Total checked.representatives) (root : IsRoot checked.representatives uv)
    (different : uv ≠ held)
    (stored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    IsolatedPending held heldHandle after := by
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
          exact observed
        exact reject_unsuccessful checked after () impossible
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
      exact isolated.through_prepared_nonempty holeKey fits admits metadata held heldHandle
        nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
        action checked after total root different stored actualNarrowed nonempty encoded selectedPrepared observed

/-- Every retained core of the actual real prefix preserves the earlier isolated boundary. -/
theorem prefix_isolated_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (workFuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (held heldHandle : Nat) (value : Node)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    uv ≠ held ∧
      match runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query with
      | .stopped _ _ => True
      | .parked checked candidate _ =>
          IsolatedPending held heldHandle checked ∧
            ∀ after, candidate = some after → IsolatedPending held heldHandle after.core
      | .narrowed checked _ _ _ _ candidate _ _ =>
          IsolatedPending held heldHandle checked ∧
            ∀ after, candidate = some after → IsolatedPending held heldHandle after.core
 := by
  classical
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  have different := packet_restart_ne formulas solver inventory caller memos metadata before
    held heldHandle uv value stop order packet isolated decoded boundary chosen
  refine ⟨different, ?_⟩
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readSuccess : Success (getValue workFuel uv) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have readFrame := (getValue_frame workFuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
    have readReady := (EnumerationDriver.getValue_ready workFuel uv before.core readAfter _ ready readSuccess).1
    have readIsolated := isolated.through_frame readFrame
    by_cases checkedResult : ∃ (repeated : Bool) (checked : Core),
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter) = [.ok (repeated, checked)]
    · obtain ⟨repeated, checked, checking⟩ := checkedResult
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap workFuel uv oldHandle scs) readAfter repeated checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have checkedIsolated := readIsolated.through_checkRepeated caller.checked.native.machine.heap
        held heldHandle workFuel uv oldHandle scs readAfter checked repeated readReady different checkSuccess
      cases repeated with
      | true =>
          unfold runPrefix runPrefixWithNarrow
          simp only [reading, checking]
          refine ⟨checkedIsolated, ?_⟩
          intro after adapted
          rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
            workFuel uv oldHandle scs before after checked adapted]
          exact checkedIsolated
      | false =>
          have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
            caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter checked
            (readFrame.total ready.safe.1.total) checkSuccess
          have wholeFrame := readFrame.trans checkFrame
          have checkedRoot : IsRoot checked.representatives uv :=
            ⟨ready.root.choose, (wholeFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
          have readStored := (EnumerationDriver.getValue_root workFuel uv before.core readAfter _
            ready.safe ready.inside ready.root readSuccess).2.2.2
          have checkedStored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
            simpa only [checkFrame.values] using readStored
          have noCandidate : IsolatedPending held heldHandle checked ∧
              ∀ after, (none : Option Cached) = some after → IsolatedPending held heldHandle after.core := by
            refine ⟨checkedIsolated, ?_⟩
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
                  workFuel workFuel uv oldHandle scs oldValue caller.checked.native.machine.heap with
              | failed fault heap =>
                  exact noCandidate
              | done pair heap =>
                  obtain ⟨narrowedValue, possibleAction⟩ := pair
                  cases possibleAction with
                  | none =>
                      exact noCandidate
                  | some action =>
                      by_cases ran : ∃ observed : Core,
                          ExceptT.run (action checked) = [.ok ((), observed)]
                      · obtain ⟨observed, raw⟩ := ran
                        have actionSuccess : Success action checked () observed := by
                          rw [Success, raw]
                          exact List.mem_singleton_self _
                        have actionIsolated := prepared_action_isolated holeKey fits admits metadata
                          held heldHandle workFuel workFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed checkedIsolated
                          (wholeFrame.total ready.safe.1.total) checkedRoot different checkedStored
                          preparedEq actionSuccess
                        simp only [raw]
                        cases encoded : encodeNode narrowedValue with
                        | none =>
                            exact noCandidate
                        | some newHandle =>
                            cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap workFuel
                                uv oldHandle newHandle scs before observed with
                            | none =>
                                exact noCandidate
                            | some attached =>
                                have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core heap
                                  workFuel uv oldHandle newHandle scs before attached observed adapted
                                have attachedIsolated : IsolatedPending held heldHandle attached.core := by
                                  rw [attachedCore]
                                  exact actionIsolated
                                have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                    graph templates workFuel metadata uv (.inr newHandle) attached.core) =
                                    [.ok ((false, metadata), attached.core)] := by
                                  rw [SourcePruningRecordTypes.recordTypes_inr]
                                  rfl
                                simp only [recorded]
                                refine ⟨checkedIsolated, ?_⟩
                                intro after candidate
                                cases candidate
                                exact attachedIsolated
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
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .stopped (ExceptT.run (getValue workFuel uv before.core))
            (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter))) := by
        unfold runPrefix runPrefixWithNarrow
        simp only [reading]
        split
        · exact (checkedResult ⟨true, _, by assumption⟩).elim
        · exact (checkedResult ⟨false, _, by assumption⟩).elim
        · rfl
      simp only [stopped]
  · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .stopped (ExceptT.run (getValue workFuel uv before.core)) none := by
      unfold runPrefix runPrefixWithNarrow
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    simp only [stopped]

end MicroCFTA.SourcePruningEnumerationSelectedStep

#print axioms MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_isolated_at_original_budget
