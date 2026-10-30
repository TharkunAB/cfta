import MicroCFTA.SourcePruningEnumerationFiniteReceiptResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptResources
import MicroCFTA.SourcePruningEnumerationExecutionCallbackBridge
import MicroCFTA.SourcePruningEnumerationExecutionCallbackControl

/-!
# Internal resource and execution-path receipt composition

The smaller-depth execution premise is an internal induction hypothesis.
Each completed receipt keeps its actual recording and recursive call paths.
The original-input theorem must derive the induction premises.
-/

namespace MicroCFTA.SourcePruningEnumerationExecutionReceiptBridge.Native
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (FullReceiptPaths OutcomePaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationExecutionPaths (LeftPaths ResumeNative ResumePrepared)
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- Retain the receipt resource result and its literal callback execution paths. -/
theorem receipt_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked) (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : match (generalizing := false) receipt with
      | .complete _ _ _ after => SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop)
    (receiptPaths : FullReceiptPaths P receipt)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      suspendedBound nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            LeftPaths P
              (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
                (fuel + extra) recursiveFuel)
              (NativeFailurePaths P)
              (continueWith
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (fuel + extra) recursiveFuel)
                graph templates stop order (fuel + extra) metadata uv)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after
        | _ => True) ∧
      OutcomePaths P (NativeFailurePaths P) outcome := by
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      have originalResources : OutcomeResources (Typing := Typing) formulas solver reached seed
          (.complete [] reached final.query) := by
        refine ⟨reached, next, final, Post.refl post.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact False.elim (List.not_mem_nil member)
      have growth := SourcePruningEnumerationFiniteReservation.final_ge recursiveFuel seed ceiling
      refine ⟨0, .complete [] reached final.query, fun _ => rfl,
        originalResources.mono growth.1 growth.2, ?_, ?_⟩
      · intro _extra
        trivial
      · intro output member
        exact False.elim (List.not_mem_nil member)
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      have currentPaths : StatePaths P after.core := receiptPaths.1
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, _frame, _types, _holes, _typing,
        callback, running, resources, _framedPaths, continuing⟩ :=
        SourcePruningEnumerationExecutionCallbackBridge.Native.callback_finite_complete_resources_with_execution_ih
          holeKey fits admits formulas solver next graph templates metadata uv fragment reached final after
          checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling
          current admitted.2.2.1 bounded known selectionMembers selectionLength mass reserved
          P currentPaths projected
          (fun work updated actual saved cache =>
            SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
              work recursiveFuel updated actual saved cache)
          pathsIH
      have left : ∀ extra,
          LeftPaths P
            (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel)
            (NativeFailurePaths P)
            (continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv)
            graph templates stop order (fuel + extra) metadata uv fragment reached final.query after := by
        intro extra
        have singleton := (callback extra).2.1
        have continuedPaths := continuing extra
        apply SourcePruningEnumerationExecutionCallbackControl.native_left_of_singleton
        all_goals assumption
      have outcomePaths : OutcomePaths P (NativeFailurePaths P) outcome := by
        have actualPaths := (left 0).2.2.1
        rw [running 0] at actualPaths
        exact actualPaths
      exact ⟨fuel, outcome, running, resources, left, outcomePaths⟩

end MicroCFTA.SourcePruningEnumerationExecutionReceiptBridge.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionReceiptBridge.Prepared
open SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (FullReceiptPaths OutcomePaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationExecutionPaths (LeftPaths ResumeNative ResumePrepared)
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- Retain the receipt resource result and its literal callback execution paths. -/
theorem receipt_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked) (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : match (generalizing := false) receipt with
      | .complete _ _ _ after => SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop)
    (receiptPaths : FullReceiptPaths P receipt)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      suspendedBound nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            LeftPaths P
              (ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
                (fuel + extra) recursiveFuel)
              (PreparedFailurePaths P)
              (continueWith
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (fuel + extra) recursiveFuel)
                graph templates stop order (fuel + extra) metadata uv)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after
        | _ => True) ∧
      OutcomePaths P (PreparedFailurePaths P) outcome := by
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      have originalResources : OutcomeResources (Typing := Typing) formulas solver reached seed
          (.complete [] reached final.query) := by
        refine ⟨reached, next, final, Post.refl post.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact False.elim (List.not_mem_nil member)
      have growth := SourcePruningEnumerationPreparedReservation.final_ge recursiveFuel seed ceiling
      refine ⟨0, .complete [] reached final.query, fun _ => rfl,
        originalResources.mono growth.1 growth.2, ?_, ?_⟩
      · intro _extra
        trivial
      · intro output member
        exact False.elim (List.not_mem_nil member)
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      have currentPaths : StatePaths P after.core := receiptPaths.1
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, _frame, _types, _holes, _typing,
        callback, running, resources, _framedPaths, continuing⟩ :=
        SourcePruningEnumerationExecutionCallbackBridge.Prepared.callback_finite_complete_resources_with_execution_ih
          holeKey fits admits formulas solver next graph templates metadata uv fragment reached final after
          checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling
          current admitted.2.2.1 bounded known selectionMembers selectionLength mass reserved
          P currentPaths projected
          (fun work updated actual saved cache =>
            SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
              work recursiveFuel updated actual saved cache)
          pathsIH
      have left : ∀ extra,
          LeftPaths P
            (ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel)
            (PreparedFailurePaths P)
            (continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv)
            graph templates stop order (fuel + extra) metadata uv fragment reached final.query after := by
        intro extra
        have singleton := (callback extra).2.1
        have continuedPaths := continuing extra
        apply SourcePruningEnumerationExecutionCallbackControl.prepared_left_of_singleton
        all_goals assumption
      have outcomePaths : OutcomePaths P (PreparedFailurePaths P) outcome := by
        have actualPaths := (left 0).2.2.1
        rw [running 0] at actualPaths
        exact actualPaths
      exact ⟨fuel, outcome, running, resources, left, outcomePaths⟩

end MicroCFTA.SourcePruningEnumerationExecutionReceiptBridge.Prepared
