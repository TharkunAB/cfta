import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates
import MicroCFTA.SourcePruningEnumerationContinuationHead
import MicroCFTA.SourcePruningEnumerationFiniteHeadCoverage
import MicroCFTA.SourcePruningEnumerationContinuationInvocation
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Coverage of an indexed finite recursive sibling scan

A supported original prefix either reaches the chosen accepting head or stops
at a strictly earlier recursive hook. The completed prefix fixes the occurrence
of each edge. Each event keeps its actual input and head memo states.
The chosen hook can stop after its head has been reached.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
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
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
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

/-- A supported indexed prefix reaches its accepting head or retains an exact earlier hook stop. -/
theorem alternatives_finite_complete_resources_accepting
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
      ∀ extra,
        let work := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
          graph templates stop order work metadata uv
        ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint), selectedEdges[index]? = some chosen →
          (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
            SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient chosen (assignment uv) →
            ∃ (eventIndex : Nat) (eventEdge : EdgeValue Symbol Constraint)
              (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
              (prefixReceipts : List (Receipt (bits + 2))) (prefixOutputs : List (Output (bits + 2) Typing))
              (fragment : Fragment) (branchCaller : Caller (bits + 2)) (branchQueries : Queries)
              (afterCache : Cached) (branchInventory : Inventory) (branchMemos : Memos),
              eventIndex ≤ index ∧ selectedEdges[eventIndex]? = some eventEdge ∧
              prefixReceipts.length = eventIndex ∧
              Post formulas solver headInventory caller headCaller headMemos ∧
              Packet formulas solver headInventory headCaller headMemos metadata before ∧
              Fits (stage recursiveFuel seed capturedMass inherited eventIndex).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited eventIndex).1)
                headCaller.checked.native.machine.heap ∧
              SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel
                (stage recursiveFuel seed capturedMass inherited eventIndex) capturedMass inherited ∧
              SourcePruningEnumerationNativeContinuations.run hook checkEmpty work work work work work
                uv scs before (selectedEdges.take eventIndex) caller memos.query =
                .complete prefixReceipts prefixOutputs headCaller headMemos.query ∧
              Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
              branchMemos.query = branchQueries ∧
              SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work uv scs
                eventEdge headCaller before headMemos.query =
                some (.complete fragment branchCaller branchQueries afterCache) ∧
              SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty work work work work work
                uv scs before selectedEdges caller memos.query fragment branchCaller branchQueries afterCache ∧
              ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited eventIndex
                (.complete fragment branchCaller branchQueries afterCache) ∧
              ((eventIndex = index ∧ eventEdge = chosen ∧
                  ∃ extended : Nat → Language.Term Symbol,
                    (∀ old < before.core.counter, extended old = assignment old) ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient caller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended before.core ∧
                    Fragments.fill extended fragment = assignment uv ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient branchCaller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended afterCache.core) ∨
                (eventIndex < index ∧
                  ∃ (hookOutputs : List (Output (bits + 2) Typing)) (reason : Failure (bits + 2) Typing)
                    (reached : Option (Caller (bits + 2) × Queries)),
                    hook fragment branchCaller branchQueries afterCache = .stopped hookOutputs reason reached ∧
                    result = .stopped prefixReceipts (prefixOutputs ++ hookOutputs)
                      (.continuation (.complete fragment branchCaller branchQueries afterCache) reason reached) ∧
                    SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
                      (stage recursiveFuel seed capturedMass inherited (eventIndex + 1))
                      (.stopped hookOutputs reason reached))) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_⟩
      · intro index receipt found
        cases found
      · intro output member
        cases member
      · intro extra index chosen found
        simp at found
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape, headAccepting⟩ :=
        SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_accepting
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
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured⟩
      · obtain ⟨unhandled, allowed, projected⟩ := unsupported
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
        · intro extra index chosen found supported ambient assignment satisfied accepted
          cases index with
          | zero =>
              have chosenSame : edge = chosen := Option.some.inj found
              subst chosen
              obtain ⟨extended, fragment, afterCache, _agree, _original, impossible, _filled, _final⟩ :=
                headAccepting ambient assignment satisfied accepted
              cases impossible
          | succ index =>
              exact (supported edge (by
                simp only [List.take_succ_cons, List.mem_cons]
                exact .inl trivial) allowed projected).elim
      · have receiptCertificate : ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited 0 receipt :=
          ⟨admitted, pending, history, cacheBounds, middleCaller, middleMemos.query, middleInventory, middleMemos,
            advanced, headPost, rfl, headFits, headKnown⟩
        cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨_actual, _next, _final, _post, _fits, _known, _same, _query, headOutputsValid⟩ := resources
            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailAccepting⟩ :=
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
            · intro extra index chosen found supported ambient assignment satisfied accepted
              let w := bound + extra
              let hook := continueWith
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                graph templates stop order w metadata uv
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      hook fragment actual queries after = .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
                    headAccepting ambient assignment satisfied accepted
                  have observed : SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w
                      uv scs edge caller before memos.query =
                      some (.complete fragment middleCaller saved afterCache) := by
                    rw [completed] at first
                    exact first
                  refine ⟨0, edge, inventory, caller, memos, [], [], fragment, middleCaller, saved,
                    afterCache, middleInventory, middleMemos, Nat.le_refl _, rfl, rfl,
                    Post.refl packet.context, packet, bounded, known, reserved.head, rfl,
                    headPost, headQueries, observed, .here observed, ?_,
                    .inl ⟨rfl, rfl, extended, agree, originalSatisfied, filled, afterSatisfied⟩⟩
                  simpa only [completed] using receiptCertificate
              | succ index =>
                  have tailFound : rest[index]? = some chosen := by
                    simpa only [List.getElem?_cons_succ] using found
                  have tailSupported : ∀ earlier ∈ rest.take index,
                      arityAllows earlier.children.length scs = true →
                      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
                    intro earlier member allowed
                    exact supported earlier (by
                      simp only [List.take_succ_cons, List.mem_cons]
                      exact .inr member) allowed
                  have realized : SourcePruningEnumerationObservation.PendingRealized
                      caller.checked.native.machine.heap before.core := by
                    obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
                    exact realized
                  have middleSatisfied :=
                    (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                      (SourceEqualityPCSGuard.holds formulas solver) ambient
                      caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      assignment realized hookPost.effects.keeps).mpr satisfied
                  have later := tailAccepting (headBound + extra) index chosen tailFound tailSupported
                    ambient assignment middleSatisfied accepted
                  have common : tailBound + (headBound + extra) = w := by dsimp [w, bound]; omega
                  rw [common] at later
                  obtain ⟨eventIndex, eventEdge, headInventory, headCaller, headMemos,
                    prefixReceipts, prefixOutputs, fragment, branchCaller, branchQueries, afterCache,
                    branchInventory, branchMemos, within, atIndex, prefixLength, inputPost, inputPacket,
                    inputFits, inputKnown, inputReserved, prefixRun, branchPost, branchQuery, observed,
                    _invocation, certificate, terminal⟩ := later
                  have liftedPrefix : SourcePruningEnumerationNativeContinuations.run hook
                      checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                      caller memos.query = .complete (receipt :: prefixReceipts)
                        (headOutputs ++ prefixOutputs) headCaller headMemos.query := by
                    have running := SourcePruningEnumerationNativeContinuations.continued_head hook
                      checkEmpty w w w w w uv scs before edge (rest.take eventIndex) caller hookCaller
                      memos.query hookQueries receipt headOutputs first (by cases receipt <;> exact continued)
                    rw [←hookQuery, prefixRun] at running
                    simpa only [List.take_succ_cons] using running
                  have newAt : (edge :: rest)[eventIndex + 1]? = some eventEdge := by
                    simpa only [List.getElem?_cons_succ] using atIndex
                  have split : (edge :: rest) = (edge :: rest).take (eventIndex + 1) ++
                      eventEdge :: (edge :: rest).drop (eventIndex + 2) := by
                    obtain ⟨inside, selectedAt⟩ := List.getElem?_eq_some_iff.mp newAt
                    have dropped := List.drop_eq_getElem_cons inside
                    rw [selectedAt] at dropped
                    rw [←dropped]
                    exact (List.take_append_drop (eventIndex + 1) (edge :: rest)).symm
                  have actualInvocation := SourcePruningEnumerationNativeContinuations.complete_prefix_invocation
                    hook checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                    caller memos.query liftedPrefix eventEdge ((edge :: rest).drop (eventIndex + 2))
                    fragment branchCaller branchQueries afterCache observed
                  rw [←split] at actualInvocation
                  refine ⟨eventIndex + 1, eventEdge, headInventory, headCaller, headMemos,
                    receipt :: prefixReceipts, headOutputs ++ prefixOutputs, fragment, branchCaller,
                    branchQueries, afterCache, branchInventory, branchMemos, by omega, newAt,
                    by simpa only [List.length_cons] using congrArg (fun n => n + 1) prefixLength,
                    hookPost.trans inputPost, inputPacket, ?_, ?_, ?_, liftedPrefix,
                    branchPost, branchQuery, observed, actualInvocation, certificate.prepend hookPost, ?_⟩
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputFits
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputKnown
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputReserved
                  · rcases terminal with ⟨sameIndex, sameEdge, extended, agree, oldSatisfied, filled, afterSatisfied⟩ |
                        ⟨earlier, hookOutputs, reason, endpoint, stoppedHook, stoppedResult, stoppedResources⟩
                    · have originalSatisfied :=
                        (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                          (SourceEqualityPCSGuard.holds formulas solver) ambient
                          caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                          extended realized hookPost.effects.keeps).mp oldSatisfied
                      exact .inl ⟨by omega, sameEdge, extended, agree, originalSatisfied, filled, afterSatisfied⟩
                    · refine .inr ⟨by omega, hookOutputs, reason, endpoint, stoppedHook, ?_, ?_⟩
                      · simp only [result, stoppedResult, List.append_assoc]
                      · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using
                          stoppedResources.post hookPost
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
            · intro extra index chosen found supported ambient assignment satisfied accepted
              let w := headBound + extra
              have observed := headRun extra
              have invoked : SourcePruningEnumerationHookInvocation.Invocation
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before (edge :: rest) caller memos.query
                  fragment actual queries after := .here observed
              have inputPrefix : SourcePruningEnumerationNativeContinuations.run
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before ((edge :: rest).take 0) caller memos.query =
                  .complete [] [] caller memos.query := rfl
              have actualSame : actual = middleCaller ∧ queries = saved := by
                simp only [advance, Option.some.injEq, Prod.mk.injEq] at advanced
                exact ⟨advanced.1, advanced.2.trans headQueries⟩
              have localPost : Post formulas solver middleInventory caller actual middleMemos := by
                simpa only [actualSame.1] using headPost
              have localQuery : middleMemos.query = queries := actualSame.2.symm.trans headQueries.symm
              refine ⟨0, edge, inventory, caller, memos, [], [], fragment, actual, queries, after,
                middleInventory, middleMemos, by omega, rfl, rfl, Post.refl packet.context,
                packet, bounded, known, reserved.head, inputPrefix, localPost, localQuery,
                observed, invoked, receiptCertificate, ?_⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, chosenFragment, chosenCache, agree, originalSatisfied,
                    completed, filled, afterSatisfied⟩ := headAccepting ambient assignment satisfied accepted
                  have equality := SourcePruningEnumerationSelectedEdge.Result.complete.inj completed
                  obtain ⟨rfl, _sameCaller, _sameQueries, rfl⟩ := equality
                  exact .inl ⟨rfl, rfl, extended, agree, originalSatisfied, filled, by
                    simpa only [actualSame.1] using afterSatisfied⟩
              | succ index =>
                  refine .inr ⟨by omega, headOutputs, reason, reached, callbackRun extra, ?_, ?_⟩
                  · rfl
                  · exact currentResources

end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
