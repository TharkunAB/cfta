import MicroCFTA.SourcePruningEnumerationCallbackMassResources
import MicroCFTA.SourcePruningEnumerationHookCertificates

/-!
# One recursive expansion after an actual edge receipt

The completed receipt derives its callback packet. An original mass ceiling
pays the actual callback. Rejected and stopped receipts continue without
emitting callback outputs. Unhandled receipts have no endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume OutcomeResources)
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
local notation "narrowSeed" => SourcePruningEnumerationExpansionAdmission.narrowSeed
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual receipt and an original mass reservation derive the exact depth-one hook. -/
theorem receipt_one_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
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
    (mass : match receipt with
      | .complete _ _ _ after => SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling
      | _ => True)
    (reserved : Reserved bits (narrowSeed seed)
      (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 1)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (reservationAdvance (narrowSeed seed)
          (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)) outcome := by
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      have originalResources : OutcomeResources (Typing := Typing) formulas solver reached seed
          (.complete [] reached final.query) := by
        refine ⟨reached, next, final, Post.refl post.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact False.elim (List.not_mem_nil member)
      have numeric := (SourceCurrentConstrainedCapEditForecast.headProfile_ge seed.2).trans
        (SourcePruningEnumerationIncomingReservation.advance_profile_ge
          (seed.1, SourceCurrentConstrainedCapEditForecast.headProfile seed.2)
          (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling))
      have alphabet := SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
        (seed.1, SourceCurrentConstrainedCapEditForecast.headProfile seed.2)
        (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)
      exact ⟨0, .complete [] reached final.query, fun _ => rfl, originalResources.mono numeric alphabet⟩
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, _frame, _types, _holes, _typing,
        _callback, running, _exactResources, resources⟩ :=
        SourcePruningEnumerationRecursive.callback_one_complete_mass_resources
          holeKey fits admits formulas solver next graph templates metadata uv fragment reached final after
          checkEmpty edgesOf stop order seed current admitted.2.2.1 bounded known selectionMembers selectionLength
          ceiling mass reserved
      exact ⟨fuel, outcome, running, resources⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
