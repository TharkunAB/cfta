import MicroCFTA.SourcePruningEnumerationFiniteSiblingResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
import MicroCFTA.SourcePruningEnumerationExecutionHeadBridge
import MicroCFTA.SourcePruningEnumerationHookInvocation

/-!
# Finite ordered siblings with actual callback execution paths

The original witnesses and resource clauses remain.
The actual fold and every actual Invocation retain paths before finish.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge.Native
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationFiniteReservation.step
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (FullReceiptPaths FoldPaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationExecutionPaths (LeftPaths ResumeNative ResumePrepared)
local notation "Metadata" => SourcePruningRecordTypes.Metadata

/-- The original sibling schedule derives the actual scan with finite-depth callbacks and all reached certificates. -/
theorem alternatives_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel)
    (inventory : Inventory)
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
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length)
    (P : EqualityTrie.Path → Prop)
    (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1 P)
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
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      FoldPaths P (NativeFailurePaths P) result ∧
      (∀ extra fragment reached saved after,
        SourcePruningEnumerationHookInvocation.Invocation
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv scs before selectedEdges caller memos.query fragment reached saved after →
        LeftPaths P
          (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel)
          (NativeFailurePaths P)
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          graph templates stop order (bound + extra) metadata uv fragment reached saved after) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_, ?_⟩
      · intro index receipt found
        cases found
      · intro output member
        cases member
      · exact ⟨fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member)⟩
      · intro extra fragment reached saved after invoked
        cases invoked
  | cons edge rest ih =>
      have headProjected : ProjectionPaths (afterHook recursiveFuel seed capturedMass inherited).1 P := by
        intro guard member
        exact projected guard
          ((SourcePruningEnumerationFiniteReservation.stage_ge recursiveFuel
            (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length).2 member)
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, receiptPaths, shape⟩ :=
        SourcePruningEnumerationExecutionHeadBridge.Native.head_finite_complete_resources_paths
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge packet ready stored decoded
          (selected edge List.mem_cons_self) incoming bounded known selectionMembers selectionLength
          capturedMass inherited initialMass inheritedLength reserved.head
          P original tails headProjected pathsIH
      have laterGrowth := SourcePruningEnumerationFiniteReservation.stage_ge recursiveFuel
        (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length
      have headGrowth := SourcePruningEnumerationFiniteReservation.afterHead_le_step recursiveFuel seed capturedMass inherited
      have wholeFits : Fits (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).2 middleCaller.checked :=
        headFits.mono (headGrowth.1.trans laterGrowth.1)
      have wholeKnown : Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).1)
          middleCaller.checked.native.machine.heap :=
        fun key resident found => laterGrowth.2 (headGrowth.2 (headKnown key resident found))
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured, callbackLeft, callbackPaths⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, [], [], middleCaller, middleInventory, middleMemos,
          .stopped [] [] (.edge (some .unhandled)), ?_, headPost,
          SourcePruningEnumerationRecursive.captured_post packet headPost, wholeFits, wholeKnown,
          by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra,
            SourcePruningEnumerationNativeBranches.advance]
        · intro index current found
          cases found
        · intro output member
          cases member
        · refine ⟨fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member), ?_⟩
          intro current observed
          cases Option.some.inj observed
          exact receiptPaths
        · intro extra fragment reached saved after invoked
          have first := headRun extra
          cases invoked with
          | here observed => rw [first] at observed; cases observed
          | completed observed _ _ => rw [first] at observed; cases observed
          | other observed _ advanced _ =>
              rw [first] at observed
              cases Option.some.inj observed
              cases advanced
      · have receiptCertificate : ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited 0 receipt :=
          ⟨admitted, pending, history, cacheBounds, middleCaller, middleMemos.query, middleInventory, middleMemos,
            advanced, headPost, rfl, headFits, headKnown⟩
        cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨_actual, _next, _final, _post, _fits, _known, _same, _query, headOutputsValid⟩ := resources
            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailPaths, tailInvocations⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail projected
            let bound := headBound + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries => .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, receipt :: processed, headOutputs ++ outputs, afterCaller, next, final, result,
              ?_, hookPost.trans tailPost, tailCaptured, tailFits, tailKnown, by simpa only [List.length_cons] using Nat.add_le_add_right tailLength 1,
              ?_, ?_, ?_, ?_, ?_⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                        graph templates stop order w metadata uv fragment actual queries after =
                        .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              have running := SourcePruningEnumerationNativeContinuations.continued_head
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                  graph templates stop order w metadata uv)
                checkEmpty w w w w w uv scs before edge rest caller hookCaller memos.query hookQueries
                receipt headOutputs first (by cases receipt <;> exact continued)
              have later := tailRun (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              rw [later] at running
              cases tailResult <;> exact running
            · intro index current found
              cases index with
              | zero =>
                  have same : receipt = current := Option.some.inj found
                  subst current
                  exact receiptCertificate
              | succ index =>
                  have member : processed[index]? = some current := by simpa only [List.getElem?_cons_succ] using found
                  exact (tailReceipts index current member).prepend hookPost
            · intro output member
              rcases List.mem_append.mp member with first | later
              · exact ⟨0, by simp, headOutputsValid output first⟩
              · obtain ⟨index, inside, certificate⟩ := tailOutputs output later
                exact ⟨index + 1, by simpa only [List.length_cons] using Nat.add_lt_add_right inside 1,
                  certificate.prepend hookPost⟩
            · rcases tailShape with completed | ⟨current, stopped, observed, certificate⟩
              · exact .inl (by simp only [result, completed])
              · exact .inr ⟨current, by simp only [result, stopped], observed,
                  certificate.prepend hookPost headOutputs⟩
            · cases tailResult with
              | complete receipts later actual queries =>
                  refine ⟨?_, ?_⟩
                  · intro current member
                    rcases List.mem_cons.mp member with same | laterMember
                    · subst current; exact receiptPaths
                    · exact tailPaths.1 current laterMember
                  · intro output member
                    rcases List.mem_append.mp member with first | laterMember
                    · exact callbackPaths output first
                    · exact tailPaths.2 output laterMember
              | stopped receipts later current =>
                  refine ⟨?_, ?_, tailPaths.2.2⟩
                  · intro currentReceipt member
                    rcases List.mem_cons.mp member with same | laterMember
                    · subst currentReceipt; exact receiptPaths
                    · exact tailPaths.1 currentReceipt laterMember
                  · intro output member
                    rcases List.mem_append.mp member with first | laterMember
                    · exact callbackPaths output first
                    · exact tailPaths.2.1 output laterMember
            · intro extra fragment reached saved after invoked
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have left := callbackLeft (w - headBound)
              rw [Nat.add_sub_of_le hl] at left
              have later := tailInvocations (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              cases invoked with
              | here observed =>
                  have same := Option.some.inj (first.symm.trans observed)
                  rw [same] at left
                  exact left
              | completed observed continued tail =>
                  have same := Option.some.inj (first.symm.trans observed)
                  rw [same] at hooked
                  obtain ⟨_outputs, rfl, rfl⟩ :=
                    SourcePruningEnumerationNativeContinuations.HookResult.complete.inj (hooked.symm.trans continued)
                  exact later fragment reached saved after tail
              | other observed notComplete advancedTail tail =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  have continued : advance receipt = some (hookCaller, hookQueries) := by
                    cases receipt with
                    | complete first actual queries cache => cases notComplete
                    | unhandled => cases advanced
                    | rejected actual queries cache | stopped fragments observation candidate =>
                        obtain ⟨_empty, actual, queries⟩ :=
                          SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                        rw [actual, queries]
                        exact advanced
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (continued.symm.trans advancedTail))
                  exact later fragment reached saved after tail
        | stopped headOutputs reason reached =>
            have currentResources := resources
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := resources
            have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
              cases receipt with
              | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
              | unhandled => cases advanced
              | rejected actual queries after | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
                  cases impossible
            obtain ⟨fragment, actual, queries, after, same⟩ := completed
            subst receipt
            refine ⟨headBound, [], headOutputs, afterCaller, next, final,
              .stopped [] headOutputs (.continuation (.complete fragment actual queries after) reason reached),
              ?_, post, SourcePruningEnumerationRecursive.captured_post packet post,
              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
            · intro extra
              simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra, callbackRun extra]
            · intro key resident found
              exact laterGrowth.2 (returnedKnown key resident found)
            · intro index current found
              cases found
            · intro output member
              exact ⟨0, by simp, outputsValid output member⟩
            · exact .inr ⟨_, rfl, observed, .inr ⟨_, reason, reached, headOutputs, [], rfl, rfl,
                receiptCertificate, currentResources⟩⟩
            · exact ⟨fun _ member => False.elim (List.not_mem_nil member), callbackPaths.1, receiptPaths, callbackPaths.2⟩
            · intro extra fragment' reached' saved' after' invoked
              have first := headRun extra
              have hooked := callbackRun extra
              cases invoked with
              | here observed =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  exact callbackLeft extra
              | completed observed continued _ =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  have impossible := hooked.symm.trans continued
                  cases impossible
              | other observed notComplete _ _ =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  cases notComplete

end MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge.Prepared
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPreparedReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint)
attribute [local irreducible] SourcePruningEnumerationPreparedReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationPreparedReservation.step
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationPreparedFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (FullReceiptPaths FoldPaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationExecutionPaths (LeftPaths ResumeNative ResumePrepared)
local notation "Metadata" => SourcePruningRecordTypes.Metadata

/-- The original sibling schedule derives the actual scan with finite-depth callbacks and all reached certificates. -/
theorem alternatives_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationPreparedRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length)
    (P : EqualityTrie.Path → Prop)
    (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1 P)
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
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      FoldPaths P (PreparedFailurePaths P) result ∧
      (∀ extra fragment reached saved after,
        SourcePruningEnumerationHookInvocation.Invocation
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv scs before selectedEdges caller memos.query fragment reached saved after →
        LeftPaths P
          (ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel)
          (PreparedFailurePaths P)
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          graph templates stop order (bound + extra) metadata uv fragment reached saved after) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_, ?_⟩
      · intro index receipt found
        cases found
      · intro output member
        cases member
      · exact ⟨fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member)⟩
      · intro extra fragment reached saved after invoked
        cases invoked
  | cons edge rest ih =>
      have headProjected : ProjectionPaths (afterHook recursiveFuel seed capturedMass inherited).1 P := by
        intro guard member
        exact projected guard
          ((SourcePruningEnumerationPreparedReservation.stage_ge recursiveFuel
            (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length).2 member)
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, receiptPaths, shape⟩ :=
        SourcePruningEnumerationExecutionHeadBridge.Prepared.head_finite_complete_resources_paths
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge packet ready stored parentAvailable parentClosed
          (selected edge List.mem_cons_self) incoming bounded known selectionMembers selectionLength
          capturedMass inherited initialMass inheritedLength reserved.head
          P original tails headProjected pathsIH
      have laterGrowth := SourcePruningEnumerationPreparedReservation.stage_ge recursiveFuel
        (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length
      have headGrowth := SourcePruningEnumerationPreparedReservation.afterHead_le_step recursiveFuel seed capturedMass inherited
      have wholeFits : Fits (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).2 middleCaller.checked :=
        headFits.mono (headGrowth.1.trans laterGrowth.1)
      have wholeKnown : Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).1)
          middleCaller.checked.native.machine.heap :=
        fun key resident found => laterGrowth.2 (headGrowth.2 (headKnown key resident found))
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured, callbackLeft, callbackPaths⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, [], [], middleCaller, middleInventory, middleMemos,
          .stopped [] [] (.edge (some .unhandled)), ?_, headPost,
          SourcePruningEnumerationRecursive.captured_post packet headPost, wholeFits, wholeKnown,
          by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra,
            SourcePruningEnumerationNativeBranches.advance]
        · intro index current found
          cases found
        · intro output member
          cases member
        · refine ⟨fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member), ?_⟩
          intro current observed
          cases Option.some.inj observed
          exact receiptPaths
        · intro extra fragment reached saved after invoked
          have first := headRun extra
          cases invoked with
          | here observed => rw [first] at observed; cases observed
          | completed observed _ _ => rw [first] at observed; cases observed
          | other observed _ advanced _ =>
              rw [first] at observed
              cases Option.some.inj observed
              cases advanced
      · have receiptCertificate : ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited 0 receipt :=
          ⟨admitted, pending, history, cacheBounds, middleCaller, middleMemos.query, middleInventory, middleMemos,
            advanced, headPost, rfl, headFits, headKnown⟩
        cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨_actual, _next, _final, _post, _fits, _known, _same, _query, headOutputsValid⟩ := resources
            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailPaths, tailInvocations⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (hookPost.effects.keeps.available (.node parentEntry storedEdges depth free) parentAvailable)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail projected
            let bound := headBound + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries => .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, receipt :: processed, headOutputs ++ outputs, afterCaller, next, final, result,
              ?_, hookPost.trans tailPost, tailCaptured, tailFits, tailKnown, by simpa only [List.length_cons] using Nat.add_le_add_right tailLength 1,
              ?_, ?_, ?_, ?_, ?_⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                        graph templates stop order w metadata uv fragment actual queries after =
                        .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              have running := SourcePruningEnumerationNativeContinuations.continued_head
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                  graph templates stop order w metadata uv)
                checkEmpty w w w w w uv scs before edge rest caller hookCaller memos.query hookQueries
                receipt headOutputs first (by cases receipt <;> exact continued)
              have later := tailRun (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              rw [later] at running
              cases tailResult <;> exact running
            · intro index current found
              cases index with
              | zero =>
                  have same : receipt = current := Option.some.inj found
                  subst current
                  exact receiptCertificate
              | succ index =>
                  have member : processed[index]? = some current := by simpa only [List.getElem?_cons_succ] using found
                  exact (tailReceipts index current member).prepend hookPost
            · intro output member
              rcases List.mem_append.mp member with first | later
              · exact ⟨0, by simp, headOutputsValid output first⟩
              · obtain ⟨index, inside, certificate⟩ := tailOutputs output later
                exact ⟨index + 1, by simpa only [List.length_cons] using Nat.add_lt_add_right inside 1,
                  certificate.prepend hookPost⟩
            · rcases tailShape with completed | ⟨current, stopped, observed, certificate⟩
              · exact .inl (by simp only [result, completed])
              · exact .inr ⟨current, by simp only [result, stopped], observed,
                  certificate.prepend hookPost headOutputs⟩
            · cases tailResult with
              | complete receipts later actual queries =>
                  refine ⟨?_, ?_⟩
                  · intro current member
                    rcases List.mem_cons.mp member with same | laterMember
                    · subst current; exact receiptPaths
                    · exact tailPaths.1 current laterMember
                  · intro output member
                    rcases List.mem_append.mp member with first | laterMember
                    · exact callbackPaths output first
                    · exact tailPaths.2 output laterMember
              | stopped receipts later current =>
                  refine ⟨?_, ?_, tailPaths.2.2⟩
                  · intro currentReceipt member
                    rcases List.mem_cons.mp member with same | laterMember
                    · subst currentReceipt; exact receiptPaths
                    · exact tailPaths.1 currentReceipt laterMember
                  · intro output member
                    rcases List.mem_append.mp member with first | laterMember
                    · exact callbackPaths output first
                    · exact tailPaths.2.1 output laterMember
            · intro extra fragment reached saved after invoked
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have left := callbackLeft (w - headBound)
              rw [Nat.add_sub_of_le hl] at left
              have later := tailInvocations (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              cases invoked with
              | here observed =>
                  have same := Option.some.inj (first.symm.trans observed)
                  rw [same] at left
                  exact left
              | completed observed continued tail =>
                  have same := Option.some.inj (first.symm.trans observed)
                  rw [same] at hooked
                  obtain ⟨_outputs, rfl, rfl⟩ :=
                    SourcePruningEnumerationNativeContinuations.HookResult.complete.inj (hooked.symm.trans continued)
                  exact later fragment reached saved after tail
              | other observed notComplete advancedTail tail =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  have continued : advance receipt = some (hookCaller, hookQueries) := by
                    cases receipt with
                    | complete first actual queries cache => cases notComplete
                    | unhandled => cases advanced
                    | rejected actual queries cache | stopped fragments observation candidate =>
                        obtain ⟨_empty, actual, queries⟩ :=
                          SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                        rw [actual, queries]
                        exact advanced
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (continued.symm.trans advancedTail))
                  exact later fragment reached saved after tail
        | stopped headOutputs reason reached =>
            have currentResources := resources
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := resources
            have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
              cases receipt with
              | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
              | unhandled => cases advanced
              | rejected actual queries after | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
                  cases impossible
            obtain ⟨fragment, actual, queries, after, same⟩ := completed
            subst receipt
            refine ⟨headBound, [], headOutputs, afterCaller, next, final,
              .stopped [] headOutputs (.continuation (.complete fragment actual queries after) reason reached),
              ?_, post, SourcePruningEnumerationRecursive.captured_post packet post,
              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
            · intro extra
              simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra, callbackRun extra]
            · intro key resident found
              exact laterGrowth.2 (returnedKnown key resident found)
            · intro index current found
              cases found
            · intro output member
              exact ⟨0, by simp, outputsValid output member⟩
            · exact .inr ⟨_, rfl, observed, .inr ⟨_, reason, reached, headOutputs, [], rfl, rfl,
                receiptCertificate, currentResources⟩⟩
            · exact ⟨fun _ member => False.elim (List.not_mem_nil member), callbackPaths.1, receiptPaths, callbackPaths.2⟩
            · intro extra fragment' reached' saved' after' invoked
              have first := headRun extra
              have hooked := callbackRun extra
              cases invoked with
              | here observed =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  exact callbackLeft extra
              | completed observed continued _ =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  have impossible := hooked.symm.trans continued
                  cases impossible
              | other observed notComplete _ _ =>
                  have same := Option.some.inj (first.symm.trans observed)
                  cases same
                  cases notComplete

end MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge.Prepared
