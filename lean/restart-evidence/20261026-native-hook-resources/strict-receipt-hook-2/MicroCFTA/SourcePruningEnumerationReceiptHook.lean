import MicroCFTA.SourcePruningEnumerationCallbackZero
import MicroCFTA.SourcePruningEnumerationHookCertificates

namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume)
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
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual admitted receipt derives its rendered callback or its literal rejection continuation. -/
theorem receipt_zero_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original next : Inventory) (caller reached : Caller width) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt width)
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile reached.checked) (known : Heap property reached.checked.native.machine.heap) :
    ∃ (fuel : Nat) (outcome : HookResult (Output width Typing) (Failure width Typing) width),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      match outcome with
      | .complete outputs actual saved =>
          actual = reached ∧ saved = final.query ∧
          ∀ output ∈ outputs, ∃ updated,
            Packet formulas solver next reached final updated output.cache ∧
            output.caller = reached ∧ output.queries = final.query ∧
            (output.metadata = none ∨ output.metadata = some updated)
      | .stopped outputs reason endpoint =>
          outputs = [] ∧ ∃ fragment receiptCache selected updated callbackCache,
            receipt = .complete fragment reached final.query receiptCache ∧
            reason = .exhausted selected updated callbackCache ∧ endpoint = some (reached, final.query) ∧
            Packet formulas solver next reached final updated callbackCache := by
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      exact ⟨0, .complete [] reached final.query, fun _ => rfl, rfl, rfl,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, _frame, _types, _holes, _typing,
        _shape, observed, running⟩ :=
        SourcePruningEnumerationRecursive.callback_zero_complete_resources holeKey fits admits formulas solver next
          graph templates metadata uv fragment reached final after checkEmpty edgesOf stop order profile property
          current admitted.2.2.1 bounded known
      refine ⟨fuel, outcome, fun extra => (running extra).2.2, ?_⟩
      cases outcome with
      | complete outputs actual saved =>
          obtain ⟨sameCaller, sameQuery, _fits, _known, packets⟩ := observed
          refine ⟨sameCaller, sameQuery, ?_⟩
          intro output member
          obtain ⟨outputPacket, outputCaller, outputQuery, metadataShape, _cacheShape⟩ := packets output member
          exact ⟨result.2, outputPacket, outputCaller, outputQuery, metadataShape⟩
      | stopped outputs reason endpoint =>
          obtain ⟨selected, empty, reasonSame, endpointSame, _fits, _known⟩ := observed
          exact ⟨empty, fragment, after, selected, result.2,
            EnumerationExpandableIndex.frame callbackCore after, rfl, reasonSame, endpointSame, _returned⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
