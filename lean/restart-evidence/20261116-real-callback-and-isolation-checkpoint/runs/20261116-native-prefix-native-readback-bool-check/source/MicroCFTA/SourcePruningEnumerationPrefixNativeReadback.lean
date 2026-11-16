import MicroCFTA.SourcePruningEnumerationRecursivePrefixLanguage
import MicroCFTA.SourceEqualityExposureCosts

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem actual_narrow_keeps
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value : Node) (before : Heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Available before value) :
    SourceEqualityRequiredCache.Keeps before
      (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state := by
  have pureKeeps := SourceEqualityRequiredCache.pure_keeps before semantic.ready
  have fallback (input : Node) (inputAvailable : Available before input) :
      SourceEqualityRequiredCache.Keeps before
        (SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) input before).state := by
    have read := SourceEqualityExposureCosts.nodeEdges_verified fuel input before semantic costs inputAvailable
    cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel input before with
    | done rows middle =>
        have middleKeeps : SourceEqualityRequiredCache.Keeps before middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using read.keeps
        have middleSemantic : SourceEqualityRequiredSemanticCache.SemanticReady middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using read.semantic
        have selectedResident : InternedNestedProvenance.Edges middle
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) := by
          intro edge member
          exact read.rows rows middle exposed edge (List.mem_filter.mp member).1
        have built := SourceEqualityOpenOrdinaryHead.node
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))
          middle middleSemantic selectedResident
        simpa only [SourcePruningNativeView.narrowAt, exposed, MergedSourceComparison.Result.state] using
          (middleKeeps.trans built.1)
    | unresolved | pending | exhausted =>
        simpa only [SourcePruningNativeView.narrowAt, exposed, MergedSourceComparison.Result.state,
          MergedSourceExposure.Result.state] using read.keeps
  cases value with
  | mu entry body depth ordinary => exact pureKeeps
  | empty | reference | node | union =>
      by_cases typed : metadata.types.contains uv = true
      · simpa only [SourcePruningOuterNarrow.narrow, typed, ↓reduceIte,
          MergedSourceComparison.Result.state] using pureKeeps
      · simp only [SourcePruningOuterNarrow.narrow]
        rw [ite_eq_right typed]
        exact fallback _ available

private theorem readback_prepared_state
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue : Node) (heap : Heap) :
    (SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
      fuel representativeFuel uv oldHandle scs oldValue heap).state =
      (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue heap).state := by
  unfold SourcePruningEnumerationAction.prepare SourcePruningEnumerationAction.prepareWithNarrow
  cases SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue heap <;> rfl

/-- Every actual real-prefix endpoint retains the original native handle and value. -/
theorem prefix_native_readback_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (workFuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (heldHandle : Nat) (heldValue : Node)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some heldValue)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    match runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query with
    | .stopped _ _ | .parked _ _ _ =>
        SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap caller.checked.native.machine.heap ∧
          lookupNode caller.checked.native.machine.heap heldHandle = some heldValue
    | .narrowed _ _ reached _ _ _ _ _ =>
        SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap reached.checked.native.machine.heap ∧
          lookupNode reached.checked.native.machine.heap heldHandle = some heldValue
 := by
  classical
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have initial : SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap
        caller.checked.native.machine.heap ∧
      lookupNode caller.checked.native.machine.heap heldHandle = some heldValue :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ packet.context.ready.semantic.ready, decoded⟩
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    by_cases fresh : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          workFuel uv oldHandle scs readAfter) = [.ok (false, checked)]
    · obtain ⟨checked, checking⟩ := fresh
      cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
      | none =>
          simpa only [runPrefix, runPrefixWithNarrow, reading, checking, oldDecoded] using initial
      | some oldValue =>
          have readSuccess : Success (getValue workFuel uv) before.core
              (.unenumerated (some oldHandle) scs) readAfter := by
            rw [Success, reading]
            exact List.mem_singleton_self _
          have readFrame := (getValue_frame workFuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
          have readStored := (EnumerationDriver.getValue_root workFuel uv before.core readAfter _
            ready.safe ready.inside ready.root readSuccess).2.2.2
          have originalStored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
            simpa only [readFrame.values] using readStored
          obtain ⟨old, oldLookup, oldAvailable, _oldClosed⟩ := realized uv oldHandle scs originalStored
          have same : old = oldValue := Option.some.inj (oldLookup.symm.trans oldDecoded)
          subst old
          have nativeKeeps := actual_narrow_keeps holeKey fits admits metadata workFuel uv oldValue
            caller.checked.native.machine.heap packet.context.ready.semantic packet.context.ready.costs oldAvailable
          let prepared := SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
            workFuel workFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
          have preparedKeeps : SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap prepared.state := by
            dsimp only [prepared]
            rw [readback_prepared_state]
            exact nativeKeeps
          have retainedLookup := lookupNode_keeps caller.checked.native.machine.heap prepared.state
            preparedKeeps heldHandle heldValue decoded
          have reachedFacts : SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap
                (SourceCurrentAllocatedPartialState.advance caller
                  (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩)
                  caller.fourth caller.merge).checked.native.machine.heap ∧
              lookupNode (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩)
                caller.fourth caller.merge).checked.native.machine.heap heldHandle = some heldValue :=
            ⟨preparedKeeps, retainedLookup⟩
          unfold runPrefix runPrefixWithNarrow
          simp only [reading, checking, oldDecoded]
          simp only [← SourcePruningEnumerationAction.prepare_configured_eq]
          dsimp only [prepared] at reachedFacts
          generalize preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
            workFuel workFuel uv oldHandle scs oldValue caller.checked.native.machine.heap = preparedResult
            at reachedFacts ⊢
          cases preparedResult with
          | failed fault heap => exact reachedFacts
          | done pair heap =>
              obtain ⟨value, action⟩ := pair
              cases action with
              | none => exact reachedFacts
              | some action =>
                  dsimp only
                  generalize rawEq : ExceptT.run (action checked) = rawAction
                  cases rawAction with
                  | nil => exact reachedFacts
                  | cons first rest =>
                      cases first with
                      | error fault => exact reachedFacts
                      | ok pair =>
                          obtain ⟨token, observed⟩ := pair
                          cases token
                          cases rest with
                          | cons another remaining => exact reachedFacts
                          | nil =>
                              cases encoded : encodeNode value with
                              | none => exact reachedFacts
                              | some newHandle =>
                                  dsimp only
                                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap workFuel
                                      uv oldHandle newHandle scs before observed with
                                  | none => exact reachedFacts
                                  | some attached =>
                                      dsimp only
                                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                          graph templates workFuel metadata uv (.inr newHandle) attached.core) =
                                          [.ok ((false, metadata), attached.core)] := by
                                        rw [SourcePruningRecordTypes.recordTypes_inr]
                                        rfl
                                      simp only [recorded]
                                      exact reachedFacts
    · unfold runPrefix runPrefixWithNarrow
      simp only [reading]
      generalize checkEq : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter) = rawCheck
      cases rawCheck with
      | nil => exact initial
      | cons first rest =>
          cases first with
          | error fault => exact initial
          | ok pair =>
              obtain ⟨repeated, checked⟩ := pair
              cases rest with
              | cons another remaining => cases repeated <;> exact initial
              | nil =>
                  cases repeated with
                  | true => exact initial
                  | false => exact (fresh ⟨checked, checkEq⟩).elim
  · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .stopped (ExceptT.run (getValue workFuel uv before.core)) none := by
      unfold runPrefix runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    exact initial

end MicroCFTA.SourcePruningEnumerationSelectedStep

#print axioms MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_native_readback_at_original_budget
