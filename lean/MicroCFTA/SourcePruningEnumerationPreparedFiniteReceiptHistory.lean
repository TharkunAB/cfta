import MicroCFTA.SourcePruningEnumerationPreparedFiniteCallbackHistory
import MicroCFTA.SourcePruningEnumerationHookCertificates

/-!
# A finite recursive callback from an actual edge receipt

The completed receipt derives its callback packet. The original mass
ceiling pays the recursive callback. Other handled receipts emit no
callback output. An unhandled receipt has no native endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
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

/-- One emitted callback output retains its actual false recording and admitted recursive tail. -/
def CallbackOutputHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (before : Cached)
    (uv : Nat) (fragment : Fragments.Fragment Symbol) (seed : Seed) (ceiling : Nat)
    (output : Output (bits + 2) Typing) : Prop :=
  RecursiveCallbackAdmission formulas solver inventory caller memos metadata before uv fragment recursiveFuel seed ceiling ∧
  ∃ (recorded : SourcePruningRecordTypes.Metadata Typing) (core : EnumerationState.State Symbol Constraint),
    ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv (.inl fragment) before.core) =
      [.ok ((false, recorded), core)] ∧
    EnumerationCompressionFrame.Frame before.core core ∧
    ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos recorded (EnumerationExpandableIndex.frame core before) seed ceiling
      (SourcePruningEnumerationRestart.decision stop order recorded (EnumerationExpandableIndex.frame core before)) output

/-- An actual receipt and a finite-depth contract derive the exact recursive hook. -/
theorem receipt_finite_complete_resources_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
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
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual _ after =>
            ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
              CallbackOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
                (fuel + extra) recursiveFuel next actual final metadata after uv fragment seed ceiling output
        | _ => True) := by
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      have originalResources : OutcomeResources (Typing := Typing) formulas solver reached seed
          (.complete [] reached final.query) := by
        refine ⟨reached, next, final, Post.refl post.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact False.elim (List.not_mem_nil member)
      have growth := SourcePruningEnumerationPreparedReservation.final_ge recursiveFuel seed ceiling
      exact ⟨0, .complete [] reached final.query, fun _ => rfl, originalResources.mono growth.1 growth.2, fun _ => trivial⟩
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, frame, _types, _holes, _typing,
        callback, running, resources, _returnedAdmission, histories⟩ :=
        SourcePruningEnumerationPreparedRecursive.callback_finite_complete_resources_with_history
          holeKey fits admits formulas solver next graph templates metadata uv fragment reached final after
          checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling
          current admitted.2.2.1 bounded known selectionMembers selectionLength mass reserved
      refine ⟨fuel, outcome, running, resources, ?_⟩
      intro extra output member
      by_cases rejected : result.1 = true
      · have equation := (callback extra).2.2
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
          stop order
        rw [ite_eq_left rejected] at equation
        have noOutputs : outcome = .complete [] reached final.query := (running extra).symm.trans equation
        rw [noOutputs] at member
        exact False.elim (List.not_mem_nil member)
      · have accepted : result.1 = false := by
          cases actual : result.1 with
          | false => rfl
          | true => exact False.elim (rejected actual)
        have originalAdmission : RecursiveCallbackAdmission formulas solver next reached final metadata after
            uv fragment recursiveFuel seed ceiling :=
          ⟨current, admitted.2.2.1, bounded, known, mass, reserved⟩
        have raw := (callback extra).2.1
        have pair : result = (false, result.2) := by
          cases result with
          | mk flag updated =>
              cases flag with
              | false => rfl
              | true => cases accepted
        rw [pair] at raw
        exact ⟨originalAdmission, result.2, callbackCore, raw, frame,
          histories extra accepted output member⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
