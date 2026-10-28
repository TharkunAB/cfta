import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadHistory

/-!
# Actual prepared heads with the new finite recursive callback

The original stored handle remains the captured target input. The prepared
ordinary parent supplies separate Available and closed facts. Actual head
resources and callback effects share the same caller and full memo states.
The smaller-depth contract uses the new recursive worker and failure type.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume CompleteWithHistory OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "finiteStep" => SourcePruningEnumerationPreparedReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem history_completed_supported
    (checkEmpty : Bool) (r n p h k uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge caller before queries =
      some (.complete fragment reached saved after)) :
    arityAllows edge.children.length scs = true ∧
      ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
        SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · refine ⟨allowed, ?_⟩
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge caller before queries
            allowed projected] at observed
        cases observed
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact ⟨tries, residual, rfl⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases actual : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed actual).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before queries
        rejected] at observed
    cases observed

/-- Keep the full finite producer packet and expose the actual completed head's admission. -/
theorem head_finite_complete_resources_with_receipt_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory),
      (∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      HeadCacheBounds before scs (scalar seed.2) (guardWidth seed.1) receipt ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      ((receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∨
        ∃ outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2),
          advance receipt = some (middleCaller, middleMemos.query) ∧
          (∀ extra, match (generalizing := false) receipt with
            | .complete fragment actual queries after =>
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
                  graph templates stop order (bound + extra) metadata uv fragment actual queries after = outcome
            | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
          OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome ∧
          (match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) ∧
          (∀ extra, match (generalizing := false) receipt with
            | .complete fragment actual _ after =>
                ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
                  SourcePruningEnumerationPreparedRecursive.CallbackOutputHistoryAt
                    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
                    (bound + extra) recursiveFuel middleInventory actual middleMemos metadata after uv fragment
                    (afterHead seed inherited) (massCeil seed capturedMass inherited) output
            | _ => True)) ∧
      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before checkEmpty
          uv handle scs parentEntry storedEdges depth free edge bound fragment reached queries after middleInventory middleMemos := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape⟩ :=
    head_finite_complete_resources_with_history holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge
      packet ready stored parentAvailable parentClosed selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape, ?_⟩
  have inputAdmission : HeadAdmission seed formulas solver inventory caller memos metadata before
      uv handle scs parentEntry storedEdges depth free edge := by
    obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
      seed formulas solver inventory caller memos metadata before packet bounded known
      parentEntry storedEdges depth free parentAvailable edge selected
    have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
      before.core.counter edge children own inheritedLength
    exact ⟨packet, ready, incoming, bounded, known, stored, parentAvailable, parentClosed,
      selected, reserved.edge costBound⟩
  intro fragment reached queries after completed
  have advanced : advance receipt = some (middleCaller, middleMemos.query) := by
    rcases shape with unsupported | ⟨outcome, advanced, _callback, _resources, _captured, _histories⟩
    · rw [unsupported.1] at completed
      cases completed
    · exact advanced
  have endpoint : reached = middleCaller ∧ queries = middleMemos.query := by
    rw [completed] at advanced
    change some (reached, queries) = some (middleCaller, middleMemos.query) at advanced
    exact Prod.mk.inj (Option.some.inj advanced)
  have actualPost : Post formulas solver middleInventory caller reached middleMemos := by
    rw [endpoint.1]
    exact post
  have actualAdmitted : Admitted uv (.complete fragment reached middleMemos.query after) := by
    rw [← endpoint.2]
    simpa only [completed] using admitted
  have actualHistory : FragmentHistory before.core (.complete fragment reached middleMemos.query after) := by
    rw [← endpoint.2]
    simpa only [completed] using history
  have actualPending : EnumerationReferences.PendingReferences after.core := by
    simpa only [completed, Pending] using pending
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  have afterPacket : Packet formulas solver middleInventory reached middleMemos metadata after :=
    SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment after level frontier
      actualPost.context actualAdmitted actualHistory actualPending ordered packet.bounded
  have actualRunning : ∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
      (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      uv scs edge caller before memos.query = some (.complete fragment reached queries after) := by
    intro extra
    rw [← completed]
    exact running extra
  have supported := history_completed_supported checkEmpty bound bound bound bound bound uv scs edge caller before memos.query
    fragment reached queries after (by simpa only [Nat.add_zero] using actualRunning 0)
  refine ⟨inputAdmission, actualPost, endpoint.2.symm,
    SourcePruningEnumerationRecursive.captured_post packet actualPost, afterPacket,
    ?_, ?_, ?_, ?_, ?_, ?_, supported.1, supported.2, actualRunning⟩
  · simpa only [completed] using admitted
  · simpa only [completed] using pending
  · simpa only [completed] using history
  · simpa only [completed] using cacheBounds
  · rw [endpoint.1]
    exact headFits
  · rw [endpoint.1]
    exact headKnown

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
