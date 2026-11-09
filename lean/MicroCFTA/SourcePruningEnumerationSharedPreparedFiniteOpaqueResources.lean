import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedHookInduction
import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
import MicroCFTA.SourcePruningEnumerationSharedReservationMonotonicity

/-!
# Finite callbacks from actual shared prepared opaque or terminal receipts

One actual shared child and finalizer fix the receipt. Its derived Packet
supplies the Left callback and smaller-depth hypothesis at a common bound.
The current IncomingAvoid fact is explicit. FinalizationAt retains only
the captured finalization equation. Whole-child backward meaning and
sufficient source depth are separate obligations.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure continueWith resume ResumeComplete OutcomeResources finish)
open SourcePruningEnumerationSharedSelectedOpaqueDispatch (opaque_complete_resources FinalizationAt)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "FoldResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "afterHead" => SourcePruningEnumerationSharedPreparedReservation.afterHead
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
local notation "finiteStep" => SourcePruningEnumerationSharedPreparedReservation.step
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finalizationAt_add
    (checkEmpty : Bool) (bound offset target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries) (receipt : Receipt (bits + 2))
    (prior : FinalizationAt checkEmpty bound target scs value caller before queries receipt) :
    FinalizationAt checkEmpty (bound + offset) target scs value caller before queries receipt := by
  cases receipt with
  | complete fragment reached saved after =>
      obtain ⟨middle, outer, waiting, child, finalized, meaning⟩ := prior
      refine ⟨middle, outer, waiting, ?_, ?_, meaning⟩
      · intro extra
        simpa only [Nat.add_assoc] using child (offset + extra)
      · intro extra
        simpa only [Nat.add_assoc] using finalized (offset + extra)
  | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ => trivial

/-- Current reservations derive the actual shared receipt, callback, and smaller-depth resources. -/
theorem opaque_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (target handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory)
      (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
      (folded : FoldResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        target scs value caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      receiptAdvance receipt = some (middleCaller, saved) ∧
      Admitted target receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      Fits (advance seed (scs.length + 1)).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (scs.length + 1)).1) middleCaller.checked.native.machine.heap ∧
      ((∃ fragment after, receipt = .complete fragment middleCaller saved after ∧
          Packet formulas solver middleInventory middleCaller middleMemos metadata after ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        (∃ after outer waiting, receipt = .stopped []
          (.ok (some []), middleCaller, saved, outer, waiting) (some after) ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        receipt = .rejected caller memos.query before) ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual queries after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata target fragment actual queries after = outcome
        | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target) caller memos.query (some receipt) = folded) ∧
      OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
        (finish target folded) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target) caller memos.query
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          target scs value caller before memos.query) = folded) ∧
      FinalizationAt checkEmpty bound target scs value caller before memos.query receipt := by
  have positive : 1 ≤ scalar seed.2 := Nat.le_trans bounded.stored.positive
    (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2)
  have pay := Nat.mul_le_mul_right (inherited + guardWidth seed.1 + 1) positive
  simp only [Nat.one_mul] at pay
  have costBound : scs.length + 1 ≤ SourcePruningEnumerationRecursiveReservation.edgeCount seed inherited := by
    unfold SourcePruningEnumerationRecursiveReservation.edgeCount
    omega
  obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
    headRun, headPost, headQuery, advanced, admitted, pending, history, headFits, headKnown, shape, headMeaning⟩ :=
    opaque_complete_resources seed formulas solver inventory caller memos metadata before checkEmpty target handle scs value
      packet ready stored incoming available closed dispatch bounded (reserved.1.prefix costBound) known
  have padding : SourceCurrentAllocatedNativeResourceForecast.Le
      (advance seed (scs.length + 1)).2 (afterHead seed inherited).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (afterHead seed inherited).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed costBound,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed costBound⟩
  have boundedHead := headFits.mono padding.1
  have knownHead : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
      middleCaller.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  have advancedQuery : receiptAdvance receipt = some (middleCaller, middleMemos.query) := by
    simpa only [headQuery] using advanced
  have massPay := Nat.mul_le_mul_right (inherited + guardWidth seed.1) positive
  simp only [Nat.one_mul] at massPay
  have mass : match (generalizing := false) receipt with
      | .complete _ _ _ after => suspendedBound after.core ≤ massCeil seed capturedMass inherited
      | _ => True := by
    rcases shape with completed | other
    · obtain ⟨fragment, after, same, _packet, _counter, bound⟩ := completed
      rw [same]
      dsimp only
      unfold SourcePruningEnumerationRecursiveReservation.massCeil
      omega
    · rcases other with stopped | rejected
      · obtain ⟨after, outer, waiting, same, _counter, _mass⟩ := stopped
        rw [same]
        trivial
      · rw [rejected]
        trivial
  obtain ⟨callbackFuel, outcome, callbackRun, resources⟩ :=
    receipt_induction_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver
      inventory middleInventory caller middleCaller memos middleMemos before target receipt packet headPost advancedQuery
      admitted pending history recursiveFuel recursive (afterHead seed inherited) (massCeil seed capturedMass inherited)
      boundedHead knownHead selectionMembers selectionLength (by cases receipt <;> exact mass) reserved.2
  have fullResources : OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome :=
    resources
  let folded : FoldResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
    match (generalizing := false) receipt with
    | .complete _ _ _ _ =>
        match (generalizing := false) outcome with
        | .complete outputs reached queries => .complete [receipt] outputs reached queries
        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
    | _ => .complete [receipt] [] middleCaller middleMemos.query
  have callbackAt (extra : Nat) := callbackRun (headBound + extra)
  have callbackCommon (extra : Nat) : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
  have callbackAligned (extra : Nat) :
      match (generalizing := false) receipt with
      | .complete fragment actual queries after =>
          continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (headBound + callbackFuel + extra) recursiveFuel)
            graph templates stop order (headBound + callbackFuel + extra) metadata target fragment actual queries after = outcome
      | _ => outcome = .complete [] middleCaller middleMemos.query := by
    have actual := callbackAt extra
    rw [callbackCommon extra] at actual
    exact actual
  have foldAt (extra : Nat) : SourcePruningEnumerationSharedReceiptContinuation.run
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (headBound + callbackFuel + extra) recursiveFuel)
        graph templates stop order (headBound + callbackFuel + extra) metadata target) caller memos.query (some receipt) = folded := by
    have actual := callbackAligned extra
    cases receipt with
    | unhandled | finalizeStopped _ _ _ _ => cases advancedQuery
    | complete fragment reached queries after =>
        simp only [folded, SourcePruningEnumerationSharedReceiptContinuation.run, actual]
        cases outcome <;> rfl
    | rejected reached queries after | stopped fragments observation candidate =>
        simp only [folded, SourcePruningEnumerationSharedReceiptContinuation.run, advancedQuery]
  have finished : OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
      (finish target folded) := by
    have actual := callbackAligned 0
    cases receipt with
    | unhandled | finalizeStopped _ _ _ _ => cases advancedQuery
    | complete fragment reached queries after =>
        cases outcome <;>
          simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint, OutcomeResources] using fullResources
    | rejected reached queries after | stopped fragments observation candidate =>
        rw [actual] at fullResources
        simpa only [folded, finish] using fullResources
  refine ⟨headBound + callbackFuel, receipt, middleCaller, saved, middleMemos, middleInventory,
    outcome, folded, ?_, headPost, headQuery, advanced, admitted, pending, history, headFits, headKnown,
    shape, boundedHead, knownHead, callbackAligned, foldAt, finished, ?_,
    finalizationAt_add checkEmpty headBound callbackFuel target scs value caller before memos.query receipt headMeaning⟩
  · intro extra
    have actual := headRun (callbackFuel + extra)
    rw [← Nat.add_assoc] at actual
    exact actual
  · intro extra
    have actual := headRun (callbackFuel + extra)
    rw [← Nat.add_assoc] at actual
    rw [actual]
    exact foldAt extra

end MicroCFTA.SourcePruningEnumerationSharedPreparedNativeHookResources
