import MicroCFTA.SourcePruningEnumerationSharedNativeBranchResources
import MicroCFTA.SourcePruningEnumerationSharedReceiptHook

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual continued head supplies its outputs and native endpoint before the suffix. -/
theorem continued_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller middleCaller : Caller width) (queries middleQueries : Queries)
    (receipt : Receipt width) (outputs : List Output)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some receipt)
    (continued : match (generalizing := false) receipt with
      | .complete fragment reached saved after =>
          hook fragment reached saved after = .complete outputs middleCaller middleQueries
      | _ => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance receipt = some (middleCaller, middleQueries) ∧
          outputs = []) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (receipt :: processed) (outputs ++ later) current := by
  cases receipt with
  | complete fragment reached saved after =>
      exact completed_head hook checkEmpty r n p h k target scs before edge rest caller reached middleCaller
        queries saved middleQueries fragment after outputs observed continued
  | unhandled | finalizeStopped _ _ _ _ =>
      obtain ⟨impossible, _empty⟩ := continued
      cases impossible
  | rejected reached saved after =>
      obtain ⟨advanced, empty⟩ := continued
      subst outputs
      simp only [run, observed, advanced, List.nil_append]
      cases run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries <;> rfl
  | stopped fragments observation candidate =>
      obtain ⟨advanced, empty⟩ := continued
      subst outputs
      simp only [run, observed, advanced, List.nil_append]
      cases run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries <;> rfl

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations

/-!
# Certificates for actual hook-aware alternatives

Each processed receipt and emitted output keeps its own native endpoint.
A stopped callback keeps its current receipt outside the processed prefix.
The original ordered edge prefix bounds each reached native heap.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory cost)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationSharedIncomingReservation.advance
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A processed receipt retains its own full Post and original edge-prefix resources. -/
def ReceiptAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat) (receipt : Receipt width) : Prop :=
  Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
  ∃ (reached : Caller width) (saved : SourceEndpointMemo.Memos) (next : Inventory) (final : Memos),
    advance receipt = some (reached, saved) ∧ Post formulas solver next caller reached final ∧
    final.query = saved ∧
    Fits (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).2 reached.checked ∧
    Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).1)
      reached.checked.native.machine.heap

/-- An emitted output retains its actual metadata packet and native edge-prefix resources. -/
def OutputAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat) (output : Output width Typing) : Prop :=
  ∃ (next : Inventory) (final : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing),
    Post formulas solver next caller output.caller final ∧ final.query = output.queries ∧
    Packet formulas solver next output.caller final metadata output.cache ∧
    (output.metadata = none ∨ output.metadata = some metadata) ∧
    Fits (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).2 output.caller.checked ∧
    Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).1)
      output.caller.checked.native.machine.heap

/-- Unsupported edges and exhausted hooks retain different exact stopping observations. -/
def StoppedAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat)
    (reached : Caller width) (next : Inventory) (final : Memos)
    (current : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Stop (Failure width Typing) width) : Prop :=
  current = .edge (some .unhandled) (reached, final.query) ∨
  ∃ (fragment : Fragments.Fragment Symbol) (receiptCache : Cached) (selected : Nat)
    (updated : SourcePruningRecordTypes.Metadata Typing) (callbackCache : Cached),
    current = .continuation (.complete fragment reached final.query receiptCache)
      (.exhausted selected updated callbackCache) (some (reached, final.query)) ∧
    ReceiptAt formulas solver caller before uv seed scs edges index
      (.complete fragment reached final.query receiptCache) ∧
    Packet formulas solver next reached final updated callbackCache

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {caller middle : Caller width} {before : Cached} {uv : Nat} {seed : Seed} {scs : List Suspended}
variable {edge : EdgeValue Symbol Constraint} {rest : List (EdgeValue Symbol Constraint)} {index : Nat}
variable {middleInventory : Inventory} {middleMemos : Memos}

/-- A suffix receipt retains its own endpoint under the original caller and edge prefix. -/
theorem ReceiptAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {receipt : Receipt width}
    (certificate : ReceiptAt formulas solver middle before uv
      (reservationAdvance seed (SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index receipt) :
    ReceiptAt formulas solver caller before uv seed scs (edge :: rest) (index + 1) receipt := by
  obtain ⟨admitted, pending, history, reached, saved, next, final, advanced, receiptPost, query, fits, known⟩ := certificate
  refine ⟨admitted, pending, history, reached, saved, next, final, advanced, post.trans receiptPost, query, ?_, ?_⟩
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using fits
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using known

/-- A suffix output keeps its callback cache and full memos at its own original prefix. -/
theorem OutputAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {output : Output width Typing}
    (certificate : OutputAt formulas solver middle before
      (reservationAdvance seed (SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index output) :
    OutputAt formulas solver caller before seed scs (edge :: rest) (index + 1) output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := certificate
  refine ⟨next, final, metadata, post.trans outputPost, query, packet, shape, ?_, ?_⟩
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using fits
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using known

/-- An exhausted suffix keeps the current unprocessed receipt and exact native endpoint. -/
theorem StoppedAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {reached : Caller width} {next : Inventory} {final : Memos}
    {current : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Stop (Failure width Typing) width}
    (certificate : StoppedAt formulas solver middle before uv
      (reservationAdvance seed (SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index reached next final current) :
    StoppedAt formulas solver caller before uv seed scs (edge :: rest) (index + 1) reached next final current := by
  rcases certificate with stopped | ⟨fragment, receiptCache, selected, updated, callbackCache, same, receipt, packet⟩
  · exact .inl stopped
  · exact .inr ⟨fragment, receiptCache, selected, updated, callbackCache, same, receipt.prepend post, packet⟩

end MicroCFTA.SourcePruningEnumerationSharedNativeHookResources

/-!
# Original resources for actual callback-aware alternatives

Each reached edge runs its concrete rendered callback before the next sibling.
The zero-expansion restart preserves explicit exhaustion. Native effects and
full memos pass to the suffix. Each sibling restores the captured cache and
metadata. This producer does not execute a deeper recursive subtree.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourcePruningEnumerationSharedNativeBranchCompletion (cost edgeCost)
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
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "reservationAdvance" => SourcePruningEnumerationSharedIncomingReservation.advance
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Initial current facts derive the actual rendered-callback scan and every reached prefix. -/
theorem alternatives_zero_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked) (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 0)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt formulas solver caller before uv seed scs selectedEdges index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt formulas solver caller before seed scs selectedEdges index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          StoppedAt formulas solver caller before uv seed scs selectedEdges processed.length
            afterCaller next final current) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, ?_, ?_, ?_, ?_, .inl rfl⟩
      · simpa only [cost, SourcePruningEnumerationSharedIncomingReservation.advance] using bounded
      · simpa only [cost, SourcePruningEnumerationSharedIncomingReservation.advance] using known
      · intro index receipt found
        cases found
      · intro output member
        cases member
  | cons edge rest ih =>
      obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
      have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
      have headReserved : Reserved bits seed (edgeCost scs before.core.counter edge) := reserved.prefix (by
        change edgeCost scs before.core.counter edge ≤ edgeCost scs before.core.counter edge + cost scs before.core.counter rest
        omega)
      obtain ⟨r, n, p, h, k, receipt, middleCaller, middleQueries, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, headPending, headHistory, shape, headFits, headKnown⟩ :=
        SourcePruningEnumerationSharedNativeBranchCompletion.head_complete_resources seed formulas solver inventory caller before
          checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos packet.context ready stored decoded
          realized (selected edge (by simp)) paths counts flags pending bounded headReserved known
      let headBound := r + n + p + h + k
      have headAt (w : Nat) (large : headBound ≤ w) :
          SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty w w w w w uv scs edge caller before memos.query = some receipt := by
        have rl : r ≤ w := by dsimp [headBound] at large; omega
        have nl : n ≤ w := by dsimp [headBound] at large; omega
        have pl : p ≤ w := by dsimp [headBound] at large; omega
        have hl : h ≤ w := by dsimp [headBound] at large; omega
        have kl : k ≤ w := by dsimp [headBound] at large; omega
        have actual := headRun (w - r) (w - n) w w (w - k) pl hl
        simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using actual
      have wholeFits : Fits (reservationAdvance seed (cost scs before.core.counter (edge :: rest))).2 middleCaller.checked := by
        change Fits (reservationAdvance seed (edgeCost scs before.core.counter edge + cost scs before.core.counter rest)).2 _
        rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
        exact headFits.mono (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge _ _)
      have wholeKnown : Heap (fun guard => guard ∈
          (reservationAdvance seed (cost scs before.core.counter (edge :: rest))).1)
          middleCaller.checked.native.machine.heap := by
        change Heap (fun guard => guard ∈
          (reservationAdvance seed (edgeCost scs before.core.counter edge + cost scs before.core.counter rest)).1) _
        rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
        intro key resident found
        exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge _ _ (headKnown key resident found)
      rcases shape with continued | ⟨unhandled, _allowed, _projected⟩
      · have advanced : advance receipt = some (middleCaller, middleMemos.query) := by simpa only [headQueries] using continued
        have receiptCertificate : ReceiptAt formulas solver caller before uv seed scs (edge :: rest) 0 receipt := by
          refine ⟨admitted, headPending packet.pending incoming, headHistory, middleCaller, middleMemos.query,
            middleInventory, middleMemos, advanced, headPost, rfl, ?_, ?_⟩
          · simpa only [List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headFits
          · simpa only [List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headKnown
        obtain ⟨callbackFuel, outcome, callbackRun, callbackObserved, _callbackResources⟩ := receipt_zero_complete_outcome_resources holeKey fits admits graph templates
          checkEmpty edgesOf stop order metadata formulas solver inventory middleInventory caller middleCaller memos middleMemos
          before uv receipt packet headPost advanced admitted (headPending packet.pending incoming) headHistory
          (reservationAdvance seed (edgeCost scs before.core.counter edge)) headFits headKnown
        cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨sameCaller, sameQuery, outputPackets⟩ := callbackObserved
            subst hookCaller
            subst hookQueries
            have tailReserved : Reserved bits
                (reservationAdvance seed (edgeCost scs before.core.counter edge)) (cost scs before.core.counter rest) :=
              reserved.after_prefix
            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailReceipts, tailOutputs, tailShape⟩ :=
              ih (reservationAdvance seed (edgeCost scs before.core.counter edge)) middleInventory middleCaller middleMemos
                (SourcePruningEnumerationRecursive.captured_post packet headPost)
                (lookupNode_keeps _ _ headPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) headFits tailReserved headKnown
            let bound := headBound + callbackFuel + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual saved => .complete (receipt :: receipts) (headOutputs ++ later) actual saved
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, receipt :: processed, headOutputs ++ outputs, afterCaller, next, final, result,
              ?_, headPost.trans tailPost, tailCaptured, ?_, ?_, ?_, ?_, ?_⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have cl : callbackFuel ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headAt w hl
              have hooked := callbackRun (w - callbackFuel)
              rw [Nat.add_sub_of_le cl] at hooked
              have continuedAt : match (generalizing := false) receipt with
                  | .complete fragment actual saved after =>
                      continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w 0)
                        graph templates stop order w metadata uv fragment actual saved after =
                        .complete headOutputs middleCaller middleMemos.query
                  | _ => advance receipt = some (middleCaller, middleMemos.query) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual saved after => exact hooked
                | unhandled | finalizeStopped _ _ _ _ => cases advanced
                | rejected actual saved after | stopped fragments observation candidate =>
                    exact ⟨advanced, (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult.complete.inj hooked).1⟩
              have running := SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.continued_head
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w 0)
                  graph templates stop order w metadata uv)
                checkEmpty w w w w w uv scs before edge rest caller middleCaller memos.query middleMemos.query
                receipt headOutputs first (by cases receipt <;> exact continuedAt)
              have later := tailRun (w - tailBound)
              rw [Nat.add_sub_of_le tl] at later
              rw [later] at running
              cases tailResult <;> exact running
            · simpa only [cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using tailFits
            · simpa only [cost, SourcePruningEnumerationSharedIncomingReservation.advance_add] using tailKnown
            · intro index current found
              cases index with
              | zero =>
                  have same : receipt = current := Option.some.inj found
                  subst current
                  exact receiptCertificate
              | succ index =>
                  have member : processed[index]? = some current := by simpa only [List.getElem?_cons_succ] using found
                  exact (tailReceipts index current member).prepend headPost
            · intro output member
              rcases List.mem_append.mp member with first | later
              · obtain ⟨updated, outputPacket, outputCaller, outputQuery, metadataShape⟩ := outputPackets output first
                refine ⟨0, by simp, middleInventory, middleMemos, updated, ?_, outputQuery.symm, ?_, metadataShape, ?_, ?_⟩
                · simpa only [outputCaller] using headPost
                · simpa only [outputCaller] using outputPacket
                · simpa only [outputCaller, List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headFits
                · simpa only [outputCaller, List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headKnown
              · obtain ⟨index, inside, certificate⟩ := tailOutputs output later
                exact ⟨index + 1, by simpa only [List.length_cons] using Nat.add_lt_add_right inside 1,
                  certificate.prepend headPost⟩
            · rcases tailShape with completed | ⟨current, stopped, certificate⟩
              · exact .inl (by simp only [result, completed])
              · refine .inr ⟨current, by simp only [result, stopped], ?_⟩
                exact certificate.prepend headPost
        | stopped headOutputs reason endpoint =>
            obtain ⟨empty, fragment, receiptCache, selected, updated, callbackCache,
              receiptSame, reasonSame, endpointSame, callbackPacket⟩ := callbackObserved
            subst headOutputs
            subst reason
            subst endpoint
            subst receipt
            let bound := headBound + callbackFuel
            refine ⟨bound, [], [], middleCaller, middleInventory, middleMemos,
              .stopped [] [] (.continuation (.complete fragment middleCaller middleMemos.query receiptCache)
                (.exhausted selected updated callbackCache) (some (middleCaller, middleMemos.query))),
              ?_, headPost, SourcePruningEnumerationRecursive.captured_post packet headPost,
              wholeFits, wholeKnown, ?_, ?_, ?_⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have cl : callbackFuel ≤ w := by dsimp [w, bound]; omega
              have first := headAt w hl
              have hooked := callbackRun (w - callbackFuel)
              rw [Nat.add_sub_of_le cl] at hooked
              dsimp only [w] at first hooked
              simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run, first, hooked]
            · intro index current found
              cases found
            · intro output member
              cases member
            · exact .inr ⟨_, rfl, .inr ⟨fragment, receiptCache, selected, updated, callbackCache,
                rfl, receiptCertificate, callbackPacket⟩⟩
      · subst receipt
        -- The unhandled receipt stores no endpoint. Use the literal entry endpoint.
        have originalFits : Fits (reservationAdvance seed (cost scs before.core.counter (edge :: rest))).2
            caller.checked := bounded.mono
          (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed _)
        have originalKnown : Heap (fun guard => guard ∈
            (reservationAdvance seed (cost scs before.core.counter (edge :: rest))).1)
            caller.checked.native.machine.heap := by
          intro key resident found
          exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed _ (known key resident found)
        refine ⟨headBound, [], [], caller, inventory, memos,
          .stopped [] [] (.edge (some .unhandled) (caller, memos.query)), ?_, Post.refl packet.context,
          packet, originalFits, originalKnown, ?_, ?_, .inr ⟨_, rfl, .inl rfl⟩⟩
        · intro extra
          simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
            headAt (headBound + extra) (by omega),
            SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance,
            SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.endpoint]
        · intro index current found
          cases found
        · intro output member
          cases member

end MicroCFTA.SourcePruningEnumerationSharedNativeHookResources
