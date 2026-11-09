import MicroCFTA.SourcePruningEnumerationSharedHookCertificates
import MicroCFTA.SourcePruningCallbackCompletion
import MicroCFTA.SourcePruningCallbackExact

/-!
# The actual shared zero-depth receipt hook

Current callback inputs derive the complete recordTypes return.
The shared continuation uses that exact return before restart.
Zero recursive depth retains explicit exhaustion and its actual endpoint.
No native query executes in this callback base case.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningRecordTypes
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

private theorem callback_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) :
    ∃ fuel result after,
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → SourceEndpointMemo.Memos → Cached → Option Next → Result)
            stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨fuel, result, after, success, stable, frame, afterOrder, types, holes, typing, bounded⟩ :=
    recordTypes_inl_complete_bounded graph templates level frontier metadata uv fragment before.core
      packet.safe ordered allocated packet.bounded
  refine ⟨fuel, result, after,
    SourcePruningEnumerationRecursive.callback_frame packet result.2 after stable.safe frame
      ⟨level, frontier, afterOrder⟩ bounded,
    stable, frame, types, holes, typing, ?_⟩
  intro extra
  have more := recordTypes_moreFuel graph templates fuel extra metadata uv (.inl fragment)
    before.core result after success
  have exactRaw := SourcePruningCallbackExact.recordTypes_exact graph templates (fuel + extra)
    metadata uv (.inl fragment) before.core after result more
  refine ⟨more, exactRaw, ?_⟩
  intro recur stop order
  unfold continueWith
  rw [exactRaw]
  obtain ⟨flag, updated⟩ := result
  cases flag <;> rfl

variable [DecidableEq Symbol] [DecidableEq Node]

/-- One callback bound fixes the actual zero-expansion hook and its native resources. -/
theorem callback_zero_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (profile : Profile) (alphabet : Constraint → Prop)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits profile caller.checked) (known : Heap alphabet caller.checked.native.machine.heap) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (outcome = if result.1 then .complete [] caller memos.query
        else match SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before) with
          | none => .complete [⟨some result.2, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
              caller memos.query
          | some .done => .complete [⟨none, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
              caller memos.query
          | some .stuck => .complete [] caller memos.query
          | some (.expand selected) => .stopped []
              (.exhausted selected result.2 (EnumerationExpandableIndex.frame after before))
              (some (caller, memos.query))) ∧
      (match outcome with
      | .complete outputs reached saved =>
          reached = caller ∧ saved = memos.query ∧ Fits profile reached.checked ∧
          Heap alphabet reached.checked.native.machine.heap ∧
          ∀ output ∈ outputs,
            Packet formulas solver inventory caller memos result.2 output.cache ∧
            output.caller = caller ∧ output.queries = memos.query ∧
            (output.metadata = none ∨ output.metadata = some result.2) ∧
            output.cache = EnumerationExpandableIndex.frame after before
      | .stopped outputs reason endpoint =>
          ∃ selected, outputs = [] ∧
            reason = .exhausted selected result.2 (EnumerationExpandableIndex.frame after before) ∧
            endpoint = some (caller, memos.query) ∧ Fits profile caller.checked ∧
            Heap alphabet caller.checked.native.machine.heap) ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        (∀ (recur : Metadata Typing → Caller width → SourceEndpointMemo.Memos → Cached → Option Next → Result)
            stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
        continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0)
          graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome := by
  obtain ⟨fuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  let outcome : Result := if result.1 then .complete [] caller memos.query
    else match SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame after before) with
      | none => .complete [⟨some result.2, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
          caller memos.query
      | some .done => .complete [⟨none, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
          caller memos.query
      | some .stuck => .complete [] caller memos.query
      | some (.expand selected) => .stopped []
          (.exhausted selected result.2 (EnumerationExpandableIndex.frame after before))
          (some (caller, memos.query))
  refine ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing, rfl, ?_, ?_⟩
  · dsimp only [outcome]
    by_cases accepted : result.1 = true
    · rw [ite_eq_left accepted]
      exact ⟨rfl, rfl, bounded, known, fun _ member => False.elim (List.not_mem_nil member)⟩
    · rw [ite_eq_right accepted]
      cases decision : SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) with
      | none =>
          dsimp only
          refine ⟨rfl, rfl, bounded, known, ?_⟩
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact ⟨returned, rfl, rfl, Or.inr rfl, rfl⟩
      | some next =>
          cases next with
          | done =>
              dsimp only
              refine ⟨rfl, rfl, bounded, known, ?_⟩
              intro output member
              have same := List.mem_singleton.mp member
              subst output
              exact ⟨returned, rfl, rfl, Or.inl rfl, rfl⟩
          | stuck =>
              exact ⟨rfl, rfl, bounded, known, fun _ member => False.elim (List.not_mem_nil member)⟩
          | expand selected => exact ⟨selected, rfl, rfl, rfl, bounded, known⟩
  · intro extra
    have actual := callback extra
    refine ⟨actual.1, actual.2.1, actual.2.2, ?_⟩
    rw [actual.2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0) stop order]
    dsimp only [outcome]
    by_cases accepted : result.1 = true
    · simp only [ite_eq_left accepted]
    · simp only [ite_eq_right accepted]
      cases decision : SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) with
      | none => rfl
      | some next => cases next <;> rfl

end MicroCFTA.SourcePruningEnumerationSharedRecursive

namespace MicroCFTA.SourcePruningEnumerationSharedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedRecursive (Output Failure continueWith resume)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
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
  | unhandled | finalizeStopped _ _ _ _ => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      exact ⟨0, .complete [] reached final.query, fun _ => rfl, rfl, rfl,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationSharedRecursive.receipt_packet formulas solver next reached final metadata
        before.core uv fragment after level frontier
        post.context admitted history pending ordered packet.bounded
      obtain ⟨fuel, result, callbackCore, outcome, _returned, _stable, _frame, _types, _holes, _typing,
        _shape, observed, running⟩ :=
        SourcePruningEnumerationSharedRecursive.callback_zero_complete_resources holeKey fits admits formulas solver next
          graph templates metadata uv fragment reached final after checkEmpty edgesOf stop order profile property
          current admitted.2.2.1 bounded known
      refine ⟨fuel, outcome, fun extra => (running extra).2.2.2, ?_⟩
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

/-- The actual zero-depth receipt retains its full packet and the shared outcome resources. -/
theorem receipt_zero_complete_outcome_resources
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
    (seed : SourcePruningEnumerationSharedIncomingReservation.Seed)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
    ∃ (fuel : Nat) (outcome : HookResult (Output width Typing) (Failure width Typing) width),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      (match outcome with
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
            Packet formulas solver next reached final updated callbackCache) ∧
      SourcePruningEnumerationSharedRecursive.OutcomeResources formulas solver caller seed outcome := by
  obtain ⟨fuel, outcome, stable, observed⟩ := receipt_zero_complete holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver original next caller reached memos final before
    uv receipt packet post advanced admitted pending history seed.2 (fun guard => guard ∈ seed.1) bounded known
  refine ⟨fuel, outcome, stable, observed, reached, next, final, post, bounded, known, ?_⟩
  cases outcome with
  | complete outputs actual saved =>
      obtain ⟨sameCaller, sameQueries, outputPackets⟩ := observed
      refine ⟨sameCaller, sameQueries, ?_⟩
      intro output member
      obtain ⟨updated, outputPacket, outputCaller, outputQueries, metadataShape⟩ := outputPackets output member
      refine ⟨next, final, updated, ?_, outputQueries.symm, ?_, metadataShape, ?_, ?_⟩
      · rw [outputCaller]
        exact post
      · simpa only [outputCaller] using outputPacket
      · simpa only [outputCaller] using bounded
      · simpa only [outputCaller] using known
  | stopped outputs reason endpoint =>
      obtain ⟨empty, _fragment, _receiptCache, _selected, _updated, _callbackCache,
        _receipt, _reason, endpointSame, _packet⟩ := observed
      refine ⟨Or.inr endpointSame, ?_⟩
      intro output member
      rw [empty] at member
      exact (List.not_mem_nil member).elim

end MicroCFTA.SourcePruningEnumerationSharedNativeHookResources
