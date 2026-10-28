import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingCertificates
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadProjectionHeap
import MicroCFTA.SourcePruningEnumerationContinuationHead

/-!
# Projection through actual prepared finite-depth siblings

Each actual callback executes its supplied recursive depth before the next edge.
The original schedule pays both phases at every sibling. Actual native
effects and full memos pass to the suffix. Each sibling retains the captured
enumeration cache and metadata. The prepared parent has separate availability
and closedness. Stops retain their own outputs and endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPreparedReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint finish OutcomeResources OutcomeProjectionHeap)
attribute [local irreducible] SourcePruningEnumerationPreparedReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "ProjectionHeap" => Heap
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationPreparedReservation.step
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The original sibling schedule derives the actual scan with finite-depth callbacks and all reached certificates. -/
theorem alternatives_finite_complete_resources_projection_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationPreparedRecursive.CompleteWithProjectionHeap (bits := bits) holeKey fits admits graph templates
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
    (initialProjection : ProjectionHeap caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited selectedEdges.length) (finish uv result) ∧
      OutcomeProjectionHeap (finish uv result) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_, ?_⟩
      · exact ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl,
          fun _ member => False.elim (List.not_mem_nil member)⟩
      · exact ⟨initialProjection, fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, _admitted, _pending, _history, _cacheBounds,
        headFits, headKnown, shape, _middleProjection⟩ :=
        SourcePruningEnumerationPreparedNativeHookResources.head_finite_complete_resources_projection_heap
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge
          packet ready stored parentAvailable parentClosed (selected edge List.mem_cons_self) incoming bounded known
          selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved.head initialProjection
      have laterGrowth := SourcePruningEnumerationPreparedReservation.stage_ge recursiveFuel
        (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length
      have headGrowth := SourcePruningEnumerationPreparedReservation.afterHead_le_step recursiveFuel seed capturedMass inherited
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured, projected⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, .stopped [] [] (.edge (some .unhandled)), ?_, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra,
            SourcePruningEnumerationNativeBranches.advance]
        · refine ⟨middleCaller, middleInventory, middleMemos, headPost,
            headFits.mono (headGrowth.1.trans laterGrowth.1), ?_, Or.inl rfl,
            fun _ member => False.elim (List.not_mem_nil member)⟩
          intro key resident found
          exact laterGrowth.2 (headGrowth.2 (headKnown key resident found))
        · exact ⟨True.intro, fun _ member => False.elim (List.not_mem_nil member)⟩
      · cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨_actual, _next, _final, _post, _fits, _known, _same, _query, headOutputsValid⟩ := resources
            obtain ⟨hookProjection, headOutputHeaps⟩ := projected
            obtain ⟨tailBound, tailResult, tailRun, tailResources, tailProjection⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (hookPost.effects.keeps.available (.node parentEntry storedEdges depth free) parentAvailable)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail hookProjection
            let bound := headBound + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries => .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, result, ?_, ?_, ?_⟩
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
            · have originalTail := tailResources.post hookPost
              cases tailResult with
              | complete processed later finalCaller finalQueries =>
                  obtain ⟨actual, next, final, post, fits, known, same, query, outputsValid⟩ := originalTail
                  refine ⟨actual, next, final, post, fits, known, same, query, ?_⟩
                  intro output member
                  rcases List.mem_append.mp member with first | later
                  · exact (headOutputsValid output first).mono laterGrowth.1 laterGrowth.2
                  · exact outputsValid output later
              | stopped processed later current =>
                  obtain ⟨actual, next, final, post, fits, known, observed, outputsValid⟩ := originalTail
                  refine ⟨actual, next, final, post, fits, known, observed, ?_⟩
                  intro output member
                  rcases List.mem_append.mp member with first | later
                  · exact (headOutputsValid output first).mono laterGrowth.1 laterGrowth.2
                  · exact outputsValid output later
            · cases tailResult with
              | complete processed later finalCaller finalQueries | stopped processed later current =>
                  refine ⟨tailProjection.1, ?_⟩
                  intro output member
                  rcases List.mem_append.mp member with first | later
                  · exact headOutputHeaps output first
                  · exact tailProjection.2 output later
        | stopped headOutputs reason reached =>
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
            refine ⟨headBound, .stopped [] headOutputs
              (.continuation (.complete fragment actual queries after) reason reached), ?_, ?_, projected⟩
            · intro extra
              simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra, callbackRun extra]
            · refine ⟨afterCaller, next, final, post, returnedFits.mono laterGrowth.1, ?_, observed, ?_⟩
              · intro key resident found
                exact laterGrowth.2 (returnedKnown key resident found)
              · intro output member
                exact (outputsValid output member).mono laterGrowth.1 laterGrowth.2

end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
