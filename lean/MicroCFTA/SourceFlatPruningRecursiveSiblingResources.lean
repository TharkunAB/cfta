import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates
import MicroCFTA.SourcePruningEnumerationContinuationHead
import MicroCFTA.SourceFlatPruningRecursiveHeadResources
import MicroCFTA.SourceFlatPruningContinuationHead
import MicroCFTA.SourceFlatPruningRecursiveBase

/-!
# Original resources for a finite-depth ordered sibling scan

Each actual callback executes its supplied recursive depth before the next edge.
The original schedule pays both phases at every sibling. Actual native
effects and full memos pass to the suffix. Each sibling retains the captured
enumeration cache and metadata. Stops retain their own outputs and endpoint.
-/
namespace MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (stage ScanReserved)
open SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "FlatOutput" => SourceFlatPruningRecursive.Output
local notation "FlatFailure" => SourceFlatPruningRecursive.Failure
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationFiniteReservation.step
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}

universe u v

private theorem ordered_append {Left : Type u} {Right : Type v} {relation : Left → Right → Prop}
    {first last : List Left} {before after : List Right}
    (head : SourceFlatPruningNativeBranches.OrderedRelated relation first before)
    (tail : SourceFlatPruningNativeBranches.OrderedRelated relation last after) :
    SourceFlatPruningNativeBranches.OrderedRelated relation (first ++ last) (before ++ after) := by
  induction head with
  | nil => exact tail
  | cons related _ ih => exact .cons related ih

private theorem continued_hook
    (hook : Fragments.Fragment Symbol → Caller (bits + 2) → SourceEndpointMemo.Memos → FlatCached →
      SourceFlatPruningNativeContinuations.HookResult (FlatOutput (bits + 2) Typing)
        (FlatFailure (bits + 2) Typing) (bits + 2))
    (receipt : Receipt (bits + 2)) (flatReceipt : FlatReceipt (bits + 2))
    (middleCaller hookCaller : Caller (bits + 2)) (middleQueries hookQueries : SourceEndpointMemo.Memos)
    (headOutputs : List (Output (bits + 2) Typing))
    (advanced : advance receipt = some (middleCaller, middleQueries))
    (compared : SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt)
    (observed : match (generalizing := false) flatReceipt with
      | .complete fragment actual saved after =>
          ∃ flatOutcome, hook fragment actual saved after = flatOutcome ∧
            SourceFlatPruningRecursive.ResultRelated flatOutcome (.complete headOutputs hookCaller hookQueries)
      | _ => SourceFlatPruningRecursive.ResultRelated
          (.complete [] middleCaller middleQueries) (.complete headOutputs hookCaller hookQueries)) :
    ∃ flatOutputs,
      SourceFlatPruningNativeBranches.OrderedRelated SourceFlatPruningRecursive.OutputRelated flatOutputs headOutputs ∧
      match (generalizing := false) flatReceipt with
      | .complete fragment actual saved after =>
          hook fragment actual saved after = .complete flatOutputs hookCaller hookQueries
      | _ => SourceFlatPruningNativeBranches.advance flatReceipt = some (hookCaller, hookQueries) ∧
          flatOutputs = [] := by
  cases flatReceipt with
  | complete fragment actual saved after =>
      obtain ⟨flatOutcome, actualHook, relatedHook⟩ := observed
      cases flatOutcome with
      | stopped _ _ _ => cases relatedHook
      | complete flatOutputs returned savedQueries =>
          obtain ⟨outputsRelated, callerSame, querySame⟩ := relatedHook
          subst returned
          subst savedQueries
          exact ⟨flatOutputs, outputsRelated, actualHook⟩
  | unhandled | rejected _ _ _ | stopped _ _ _ =>
      obtain ⟨outputsRelated, callerSame, querySame⟩ := observed
      have actualAdvance := SourceFlatPruningRecursive.advance_related _ receipt compared
      refine ⟨[], outputsRelated, ?_, rfl⟩
      rw [actualAdvance, advanced, callerSame, querySame]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The original sibling schedule derives the actual scan with finite-depth callbacks and all reached certificates. -/
theorem alternatives_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourceFlatPruningRecursive.Complete (bits := bits) holeKey fits admits graph templates
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
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length) :
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
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatFold,
          SourceFlatPruningNativeContinuations.run
            (SourceFlatPruningRecursive.continueWith
              (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                stop order (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata uv)
            checkEmpty (bound + extra) (bound + extra) (bound + extra)
            uv scs flat selectedEdges caller memos.query = flatFold ∧
          SourceFlatPruningNativeContinuations.ResultRelated SourceFlatPruningRecursive.OutputRelated
            SourceFlatPruningRecursive.FailureRelated flatFold result) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_⟩
      · intro index receipt found
        cases found
      · intro output member
        cases member
      · intro flat _related extra
        exact ⟨.complete [] [] caller memos.query, rfl, .nil, .nil, rfl, rfl⟩
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape, headFlat⟩ :=
        SourceFlatPruningNativeHookResources.head_finite_complete_resources
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge packet ready stored decoded
          (selected edge List.mem_cons_self) incoming bounded known selectionMembers selectionLength
          capturedMass inherited initialMass inheritedLength reserved.head
      have laterGrowth := SourcePruningEnumerationFiniteReservation.stage_ge recursiveFuel
        (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length
      have headGrowth := SourcePruningEnumerationFiniteReservation.afterHead_le_step recursiveFuel seed capturedMass inherited
      have wholeFits : Fits (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).2 middleCaller.checked :=
        headFits.mono (headGrowth.1.trans laterGrowth.1)
      have wholeKnown : Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).1)
          middleCaller.checked.native.machine.heap :=
        fun key resident found => laterGrowth.2 (headGrowth.2 (headKnown key resident found))
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured, flatCallbackRun⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, [], [], middleCaller, middleInventory, middleMemos,
          .stopped [] [] (.edge (some .unhandled)), ?_, headPost,
          SourcePruningEnumerationRecursive.captured_post packet headPost, wholeFits, wholeKnown,
          by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra,
            SourcePruningEnumerationNativeBranches.advance]
        · intro index current found
          cases found
        · intro output member
          cases member
        · intro flat related extra
          obtain ⟨flatReceipt, actualHead, compared⟩ := headFlat flat related extra
          have same : flatReceipt = .unhandled := by
            cases flatReceipt <;> simp only [SourceFlatPruningSelectedEdge.ResultRelated] at compared
            rfl
          subst flatReceipt
          refine ⟨.stopped [] [] (.edge (some .unhandled)), ?_, .nil, .nil, trivial⟩
          simp only [SourceFlatPruningNativeContinuations.run, actualHead,
            SourceFlatPruningNativeBranches.advance]
      · have receiptCertificate : ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited 0 receipt :=
          ⟨admitted, pending, history, cacheBounds, middleCaller, middleMemos.query, middleInventory, middleMemos,
            advanced, headPost, rfl, headFits, headKnown⟩
        cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨_actual, _next, _final, _post, _fits, _known, _same, _query, headOutputsValid⟩ := resources
            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailFlat⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail
            let bound := headBound + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries => .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, receipt :: processed, headOutputs ++ outputs, afterCaller, next, final, result,
              ?_, hookPost.trans tailPost, tailCaptured, tailFits, tailKnown, by simpa only [List.length_cons] using Nat.add_le_add_right tailLength 1,
              ?_, ?_, ?_, ?_⟩
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
            · intro flat related extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              obtain ⟨flatReceipt, actualHead, comparedHead⟩ := headFlat flat related (w - headBound)
              rw [Nat.add_sub_of_le hl] at actualHead
              have actualHook := flatCallbackRun (w - headBound) flatReceipt comparedHead
              rw [Nat.add_sub_of_le hl] at actualHook
              obtain ⟨flatHeadOutputs, headOutputsRelated, flatContinued⟩ := continued_hook
                (SourceFlatPruningRecursive.continueWith
                  (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                    stop order w recursiveFuel) graph templates stop order w metadata uv)
                receipt flatReceipt middleCaller hookCaller middleMemos.query hookQueries headOutputs
                advanced comparedHead actualHook
              obtain ⟨flatTail, actualTail, comparedTail⟩ := tailFlat flat related (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at actualTail
              let flatResult : SourceFlatPruningNativeContinuations.Result
                  (FlatOutput (bits + 2) Typing) (FlatFailure (bits + 2) Typing) (bits + 2) :=
                match (generalizing := false) flatTail with
                | .complete receipts later actual queries =>
                    .complete (flatReceipt :: receipts) (flatHeadOutputs ++ later) actual queries
                | .stopped receipts later current =>
                    .stopped (flatReceipt :: receipts) (flatHeadOutputs ++ later) current
              refine ⟨flatResult, ?_, ?_⟩
              · have running := SourceFlatPruningNativeContinuations.continued_head
                  (SourceFlatPruningRecursive.continueWith
                    (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                      stop order w recursiveFuel) graph templates stop order w metadata uv)
                  checkEmpty w w w uv scs flat edge rest caller hookCaller memos.query hookQueries
                  flatReceipt flatHeadOutputs actualHead (by cases flatReceipt <;> exact flatContinued)
                rw [actualTail] at running
                cases flatTail <;> exact running
              · cases flatTail <;> cases tailResult <;>
                  simp only [SourceFlatPruningNativeContinuations.ResultRelated] at comparedTail <;> try contradiction
                case complete.complete flatProcessed flatOutputs flatCaller flatQueries
                    oldProcessed oldOutputs oldCaller oldQueries =>
                  obtain ⟨receipts, outputsRelated, callerSame, queriesSame⟩ := comparedTail
                  exact ⟨.cons comparedHead receipts, ordered_append headOutputsRelated outputsRelated,
                    callerSame, queriesSame⟩
                case stopped.stopped flatProcessed flatOutputs flatCurrent oldProcessed oldOutputs oldCurrent =>
                  obtain ⟨receipts, outputsRelated, current⟩ := comparedTail
                  exact ⟨.cons comparedHead receipts, ordered_append headOutputsRelated outputsRelated, current⟩
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
              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_⟩
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
            · intro flat related extra
              obtain ⟨flatReceipt, actualHead, comparedHead⟩ := headFlat flat related extra
              cases flatReceipt with
              | unhandled | rejected _ _ _ | stopped _ _ _ => cases comparedHead
              | complete flatFragment flatCaller flatQueries flatAfter =>
                  have retainedCompared := comparedHead
                  obtain ⟨fragmentSame, callerSame, querySame, _caches⟩ := comparedHead
                  subst flatFragment
                  subst flatCaller
                  subst flatQueries
                  obtain ⟨flatOutcome, actualHook, comparedHook⟩ :=
                    flatCallbackRun extra (.complete fragment actual queries flatAfter) retainedCompared
                  cases flatOutcome with
                  | complete _ _ _ => cases comparedHook
                  | stopped flatOutputs flatReason flatReached =>
                      obtain ⟨outputsRelated, reasonRelated, reachedSame⟩ := comparedHook
                      subst flatReached
                      refine ⟨.stopped [] flatOutputs
                        (.continuation (.complete fragment actual queries flatAfter) flatReason reached),
                        ?_, .nil, outputsRelated, retainedCompared, reasonRelated, rfl⟩
                      exact SourceFlatPruningNativeContinuations.stopped_hook
                        (SourceFlatPruningRecursive.continueWith
                          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                            stop order (headBound + extra) recursiveFuel)
                          graph templates stop order (headBound + extra) metadata uv)
                        checkEmpty (headBound + extra) (headBound + extra) (headBound + extra)
                        uv scs flat edge rest caller actual memos.query queries fragment flatAfter
                        flatOutputs flatReason reached actualHead actualHook

/-- Retain the complete sibling result and resources for its exact finished outcome. -/
theorem alternatives_finite_finish_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourceFlatPruningRecursive.Complete (bits := bits) holeKey fits admits graph templates
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
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length) :
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
      SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited selectedEdges.length)
        (SourcePruningEnumerationRecursive.finish uv result) ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatFold,
          SourceFlatPruningNativeContinuations.run
            (SourceFlatPruningRecursive.continueWith
              (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                stop order (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata uv)
            checkEmpty (bound + extra) (bound + extra) (bound + extra)
            uv scs flat selectedEdges caller memos.query = flatFold ∧
          SourceFlatPruningNativeContinuations.ResultRelated SourceFlatPruningRecursive.OutputRelated
            SourceFlatPruningRecursive.FailureRelated flatFold result) := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result,
    observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape, flatRunning⟩ :=
    alternatives_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges depth free
      packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  have outputResources : ∀ output ∈ outputs,
      SourcePruningEnumerationRecursive.OutputResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited selectedEdges.length) output := by
    intro output member
    obtain ⟨index, inside, certificate⟩ := outputCertificates output member
    have own : SourcePruningEnumerationRecursive.OutputResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited (index + 1)) output := certificate
    have growth := SourcePruningEnumerationFiniteReservation.count_mono recursiveFuel seed capturedMass inherited
      (by omega : index + 1 ≤ selectedEdges.length)
    exact own.mono growth.1 growth.2
  have actualShape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) := by
    rcases shape with completed | ⟨current, stopped, observedEndpoint, _certificate⟩
    · exact .inl completed
    · exact .inr ⟨current, stopped, observedEndpoint⟩
  have finished := SourcePruningEnumerationRecursive.finish_resources_general
    formulas solver caller uv (stage recursiveFuel seed capturedMass inherited selectedEdges.length)
    processed outputs afterCaller next final result post afterFits afterKnown outputResources actualShape
  exact ⟨bound, processed, outputs, afterCaller, next, final, result,
    observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape, finished, flatRunning⟩


end MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources
