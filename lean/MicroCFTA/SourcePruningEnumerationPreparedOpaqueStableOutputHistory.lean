import MicroCFTA.SourcePruningEnumerationPreparedOpaqueFiniteHistory

/-!
# Stable resource certificates for actual opaque output histories

The old producer runs once. Its complete result remains the first packet.
A second observer retains original resources and the same actual receipt
at every larger work bound. This module does not change the old histories.
It does not claim that a point observation alone implies a stable family.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed advance)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume CompleteWithHistory OutcomeResources finish)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
local notation "finiteStep" => SourcePruningEnumerationPreparedReservation.step
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Each actual output retains its old history and original resource admission for the same stable receipt. -/
def OpaqueOutputStableHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached) (target : Nat) (scs : List Suspended) (value : Node)
    (output : Output (bits + 2) Typing) : Prop :=
  OpaqueOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
    workFuel recursiveFuel caller memos metadata before target scs value output ∧
  ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached),
    SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
      workFuel workFuel workFuel workFuel workFuel target scs value caller before memos.query =
        some (.complete fragment reached saved after) →
    ∃ opaqueSeed : Seed, Fits opaqueSeed.2 caller.checked ∧
      SourcePruningEnumerationIncomingReservation.Reserved bits opaqueSeed (scs.length + 1) ∧
      Heap (fun guard => guard ∈ opaqueSeed.1) caller.checked.native.machine.heap ∧
      ∀ extra, SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
        (workFuel + extra) (workFuel + extra) (workFuel + extra) (workFuel + extra) (workFuel + extra)
        target scs value caller before memos.query =
          some (.complete fragment reached saved after)

/-- Forget only the added resource observer and retain the exact old history. -/
theorem OpaqueOutputStableHistoryAt.forget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached) (target : Nat) (scs : List Suspended) (value : Node)
    (output : Output (bits + 2) Typing)
    (history : OpaqueOutputStableHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel caller memos metadata before target scs value output) :
    OpaqueOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel caller memos metadata before target scs value output := history.1

/-- Keep the entire old opaque producer result and append exact stable output certificates. -/
theorem opaque_finite_complete_resources_with_stable_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
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
    (reserved : SourcePruningEnumerationPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory)
      (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
      (folded : FoldResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
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
      (∀ extra, SourcePruningEnumerationReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target) (some receipt) = folded) ∧
      OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
        (finish target folded) ∧
      (∀ extra, SourcePruningEnumerationReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target)
        (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          target scs value caller before memos.query) = folded) ∧
      (∀ extra, ∀ output ∈ SourcePruningEnumerationHookInvocation.foldOutputs folded,
        OpaqueOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel caller memos metadata before target scs value output) ∧
      (∀ extra, ∀ output ∈ SourcePruningEnumerationHookInvocation.foldOutputs folded,
        OpaqueOutputStableHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel caller memos metadata before target scs value output) := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, outcome, folded,
    headRun, headPost, headQuery, advanced, admitted, pending, history, headFits, headKnown,
    shape, paddedFits, paddedKnown, callbackRun, receiptRun, resources, opaqueFoldRun, opaqueHistories⟩ :=
    opaque_finite_complete_resources_with_history holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before target handle scs value
      packet ready stored incoming available closed dispatch bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, outcome, folded,
    headRun, headPost, headQuery, advanced, admitted, pending, history, headFits, headKnown,
    shape, paddedFits, paddedKnown, callbackRun, receiptRun, resources, opaqueFoldRun, opaqueHistories, ?_⟩
  have positive : 1 ≤ scalar seed.2 := Nat.le_trans bounded.stored.positive
    (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2)
  have pay := Nat.mul_le_mul_right (inherited + guardWidth seed.1 + 1) positive
  simp only [Nat.one_mul] at pay
  have costBound : scs.length + 1 ≤ SourcePruningEnumerationRecursiveReservation.edgeCount seed inherited := by
    unfold SourcePruningEnumerationRecursiveReservation.edgeCount
    omega
  intro extra output member
  refine ⟨opaqueHistories extra output member, ?_⟩
  intro fragment reached actualSaved after observed
  have receiptSame : receipt = .complete fragment reached actualSaved after :=
    Option.some.inj ((headRun extra).symm.trans observed)
  refine ⟨seed, bounded, reserved.1.prefix costBound, known, ?_⟩
  intro padding
  have actual := headRun (extra + padding)
  simpa only [Nat.add_assoc, receiptSame] using actual

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
