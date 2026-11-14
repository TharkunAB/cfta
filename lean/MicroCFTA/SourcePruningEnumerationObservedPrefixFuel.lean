import MicroCFTA.EnumerationExecution
import MicroCFTA.EnumerationPartialExact
import MicroCFTA.SourcePruningEnumerationRecursion
import MicroCFTA.SourcePruningEnumerationNativeIndexStability
import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

import MicroCFTA.SourcePruningEnumerationIdentityPrefixResources

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationObservedPrefixFuel
open InternedProbeProvenance SourcePruningEnumerationNodes
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- A successful read retains its complete raw result at a larger bound. -/
private theorem getValue_success_raw_moreFuel
    (fuel extra uv : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (value : UVarValue Symbol)
    (observed : Success (getValue fuel uv) before value after) :
    ExceptT.run (getValue (fuel + extra) uv before) =
      ExceptT.run (getValue fuel uv before) := by
  have retained := EnumerationExecution.getValue_moreFuel fuel extra uv before value after observed
  exact (EnumerationPartialExact.getValue_exact (fuel + extra) uv before after value retained).trans
    (EnumerationPartialExact.getValue_exact fuel uv before after value observed).symm

/-- A successful native recursion check retains its complete raw result. -/
private theorem checkRepeated_success_raw_moreFuel
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) :
    ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap
      (fuel + extra) uv handle scs before) =
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs before) := by
  cases decoded : lookupNode heap handle with
  | none => simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded]
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, reading, _continued⟩ := (success_bind _ _ _ _ _).mp observed
        have retained := EnumerationExecution.representative_moreFuel fuel extra uv
          before root resolved reading
        have oldExact := EnumerationPartialExact.representative_success_exact
          fuel uv before resolved root reading
        have newExact := EnumerationPartialExact.representative_success_exact
          (fuel + extra) uv before resolved root retained
        simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte]
        rw [bind_single _ _ before resolved root newExact,
          bind_single _ _ before resolved root oldExact]
      · simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary]

/-- A successful indexed parked adapter retains its exact cached endpoint. -/
private theorem parked_adapt_some_moreFuel
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checked : EnumerationState.State Symbol Constraint)
    (observed : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs
      before checked = some after) :
    SourcePruningEnumerationParkedRestart.adapt heap (fuel + extra) uv handle scs
      before checked = some after := by
  unfold SourcePruningEnumerationParkedRestart.adapt at observed ⊢
  rw [Option.map_eq_some_iff] at observed ⊢
  obtain ⟨saved, written, mapped⟩ := observed
  exact ⟨saved, SourcePruningEnumerationNativeIndex.write_some_moreFuel heap fuel extra uv
    (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before) saved written, mapped⟩

end MicroCFTA.SourcePruningEnumerationObservedPrefixFuel

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open SourcePruningEnumerationSharedSelectedContinuations
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Observation" => ChildDispatch.Observation
variable {width : Nat}
local notation "Fold" => NativeContinuations.Result (Output width Unit) (Failure width Unit) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq Node]

/-- The actual worker stops with no outputs on either unsupported prefix form. -/
private theorem unsupported_prefix_stops
    (child : Visitor)
    (narrow : Metadata Unit → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Unit → Nat → Bool))
    (order : Metadata Unit → List Nat → Option Nat)
    (workFuel recursiveFuel uv : Nat)
    (metadata : Metadata Unit) (caller : Caller width) (queries : Queries) (before : Cached)
    (observed : SourcePruningEnumerationSelectedStep.Result width Unit)
    (observing : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow narrow graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
      uv caller before queries = observed)
    (unsupported : match observed with
      | .stopped _ _ => True
      | .parked _ none _ => True
      | _ => False) :
    resumeWithNarrow child narrow graph templates checkEmpty edgesOf stop order workFuel
      (recursiveFuel + 1) metadata caller queries before (some (.expand uv)) =
      .stopped [] (.selected uv observed) (some (caller, queries)) := by
  cases observed with
  | stopped reading checking => simp only [resumeWithNarrow, observing]
  | parked checked candidate raw =>
      cases candidate with
      | none => simp only [resumeWithNarrow, observing]
      | some saved => cases unsupported
  | narrowed checked prepared reached saved action candidate right ordinary => cases unsupported

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

open EnumerationCorrectness EnumerationCompressionFrame InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Every supported actual identity prefix retains its complete result at a larger bound. -/
private theorem prefix_identity_supported_moreFuel
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Unit → Nat → Bool))
    (order : Metadata Unit → List Nat → Option Nat) (metadata : Metadata Unit)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (ready : SourceEqualityRequiredCache.Ready caller.checked.native.machine.heap)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (total : UnionFind.Total before.core.representatives)
    (fuel extra uv : Nat) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      (fun _ _ _ node state => .done node state) graph templates stop order metadata
      fuel fuel fuel fuel fuel fuel uv caller before queries
    match observed with
    | .stopped _ _ => True
    | .parked _ none _ => True
    | .narrowed _ (.failed _ _) _ _ _ _ _ _ => True
    | _ => SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (fun _ _ _ node state => .done node state) graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before queries = observed := by
  classical
  dsimp only
  by_cases readable : ∃ (handle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue fuel uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]
  · obtain ⟨handle, scs, readAfter, reading⟩ := readable
    have readObserved : Success (getValue fuel uv) before.core
        (.unenumerated (some handle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have laterReading : ExceptT.run (getValue (fuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)] :=
      (SourcePruningEnumerationObservedPrefixFuel.getValue_success_raw_moreFuel
        fuel extra uv before.core readAfter (.unenumerated (some handle) scs) readObserved).trans reading
    by_cases repeated : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv handle scs readAfter) = [.ok (true, checked)]
    · obtain ⟨checked, checking⟩ := repeated
      have checkObserved : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv handle scs) readAfter true checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have laterChecking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap (fuel + extra) uv handle scs readAfter) = [.ok (true, checked)] :=
        (SourcePruningEnumerationObservedPrefixFuel.checkRepeated_success_raw_moreFuel
          caller.checked.native.machine.heap fuel extra uv handle scs readAfter checked true checkObserved).trans checking
      cases adapted : SourcePruningEnumerationParkedRestart.adapt
          caller.checked.native.machine.heap fuel uv handle scs before checked with
      | none =>
          have oldResult : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph templates stop order metadata
              fuel fuel fuel fuel fuel fuel uv caller before queries =
              .parked checked none none := by
            simp only [SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
              reading, checking, adapted, Option.map_none]
          rw [oldResult]
          trivial
      | some parked =>
          have laterAdapted := SourcePruningEnumerationObservedPrefixFuel.parked_adapt_some_moreFuel
            caller.checked.native.machine.heap fuel extra uv handle scs before parked checked adapted
          have oldResult : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph templates stop order metadata
              fuel fuel fuel fuel fuel fuel uv caller before queries =
              .parked checked (some parked)
                (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))) := by
            simp only [SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
              reading, checking, adapted, Option.map_some]
          have laterResult : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph templates stop order metadata
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
              uv caller before queries =
              .parked checked (some parked)
                (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))) := by
            simp only [SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
              laterReading, laterChecking, laterAdapted, Option.map_some]
          rw [oldResult]
          exact laterResult
    · by_cases fresh : ∃ checked : Core,
          ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
            caller.checked.native.machine.heap fuel uv handle scs readAfter) = [.ok (false, checked)]
      · obtain ⟨checked, checking⟩ := fresh
        have checkObserved : Success (SourcePruningEnumerationRecursion.checkRepeated
            caller.checked.native.machine.heap fuel uv handle scs) readAfter false checked := by
          rw [Success, checking]
          exact List.mem_singleton_self _
        have laterChecking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
            caller.checked.native.machine.heap (fuel + extra) uv handle scs readAfter) = [.ok (false, checked)] :=
          (SourcePruningEnumerationObservedPrefixFuel.checkRepeated_success_raw_moreFuel
            caller.checked.native.machine.heap fuel extra uv handle scs readAfter checked false checkObserved).trans checking
        have readFrame : Frame before.core readAfter :=
          (EnumerationCompressionFrame.getValue_frame fuel uv before.core readAfter
            (.unenumerated (some handle) scs) total readObserved).1
        have entered : Frame readAfter checked :=
          SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
            caller.checked.native.machine.heap fuel uv handle scs readAfter checked
            (readFrame.total total) checkObserved
        obtain ⟨oldValue, decoded, _encoded, _available, _closed, oldEmpty, oldNonempty⟩ :=
          SourcePruningEnumerationSelectedStep.runPrefix_identity_pending graph templates stop order metadata
            caller before queries fuel fuel uv handle scs readAfter checked
            ready realized total reading checking entered
        obtain ⟨laterValue, laterDecoded, _laterEncoded, _laterAvailable, _laterClosed, laterEmpty, laterNonempty⟩ :=
          SourcePruningEnumerationSelectedStep.runPrefix_identity_pending graph templates stop order metadata
            caller before queries (fuel + extra) (fuel + extra) uv handle scs readAfter checked
            ready realized total laterReading laterChecking entered
        have same : laterValue = oldValue := Option.some.inj (laterDecoded.symm.trans decoded)
        subst laterValue
        by_cases empty : oldValue = .empty
        · rw [oldEmpty empty fuel fuel fuel fuel]
          exact laterEmpty empty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        · rw [oldNonempty empty fuel fuel fuel fuel]
          exact laterNonempty empty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
      · have oldResult : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
            (fun _ _ _ node state => .done node state) graph templates stop order metadata
            fuel fuel fuel fuel fuel fuel uv caller before queries =
            .stopped (ExceptT.run (getValue fuel uv before.core))
              (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv handle scs readAfter))) := by
          unfold SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          rw [reading]
          dsimp only
          split
          · exact (repeated ⟨_, by assumption⟩).elim
          · exact (fresh ⟨_, by assumption⟩).elim
          · rfl
        rw [oldResult]
        trivial
  · have oldResult : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (fun _ _ _ node state => .done node state) graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before queries =
        .stopped (ExceptT.run (getValue fuel uv before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [oldResult]
    trivial

variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Every supported identity prefix retains its packet and resources at any bound. -/
theorem prefix_identity_resources_at_any_budget
    (graph : Graph Symbol Constraint)
    (metadata : Metadata Unit)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (fuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none)
      metadata before = some (.expand selected)) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
      fuel fuel fuel fuel fuel fuel selected caller before memos.query
    match observed with
    | .stopped _ _ => True
    | .parked _ none _ => True
    | .narrowed _ (.failed _ _) _ _ _ _ _ _ => True
    | _ => CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory
        selected caller before memos profile property observed
    := by
  classical
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨bound, sufficient⟩ := prefix_identity_complete_resources
    graph false (fun _ => []) metadata formulas solver inventory caller memos before
    packet profile property bounded known
  have replay := prefix_identity_supported_moreFuel graph [] none (fun _ _ => none) metadata
    caller before memos.query packet.context.ready.good.heap realized packet.safe.1.total
    fuel bound selected
  have large := sufficient fuel selected chosen
  have largeAt : CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory
      selected caller before memos profile property
      (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
        (fuel + bound) (fuel + bound) (fuel + bound) (fuel + bound) (fuel + bound) (fuel + bound)
        selected caller before memos.query) := by
    simpa only [Nat.add_comm bound fuel] using large
  dsimp only at replay ⊢
  generalize observedEq : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
    (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
    fuel fuel fuel fuel fuel fuel selected caller before memos.query = observed at replay ⊢
  cases observed with
  | stopped reading checking => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after => simpa only [replay] using largeAt
  | narrowed checked prepared reached saved action candidate right ordinary =>
      cases prepared with
      | failed fault heap => trivial
      | done payload heap => simpa only [replay] using largeAt

end MicroCFTA.SourcePruningEnumerationSharedRecursive
