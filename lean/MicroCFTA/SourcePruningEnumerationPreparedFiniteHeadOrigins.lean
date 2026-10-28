import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeOrigins
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage

/-!
# Original term paths at an actual prepared finite head

The complete prepared head resource packet is retained first.
The prepared parent supplies Available and closed facts separately from the
original stored handle. An original model and accepted edge construct the
same actual captured receipt. The new recursive callback keeps its exact
resource outcome. Its later outputs are not given a semantic model here.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open SourcePruningEnumerationOrigins
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume Complete OutcomeResources)
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

/-- Retain every prepared head resource and construct its actual accepted captured receipt. -/
theorem head_finite_complete_resources_origins
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
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
      ((∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
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
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True)) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol) (whole : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        AssignmentOrigins whole before.core.counter assignment →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment middleCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core ∧
          AssignmentOrigins whole afterCache.core.counter extended := by
  have recursive := SourcePruningEnumerationPreparedRecursive.finite_complete
    (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, resources⟩ :=
    head_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs
      parentEntry storedEdges depth free edge packet ready stored parentAvailable parentClosed selected incoming
      bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, resources, ?_⟩
  intro ambient assignment whole satisfied accepted origins
  obtain ⟨running, _headPost, headQueries, _admitted, _pendingReceipt, _history,
    _cacheBounds, _headFits, _headKnown, headShape⟩ := resources
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have inheritedModel : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    have model := satisfied.1.2 uv
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at model
    exact model.2
  obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry storedEdges depth free edge scs packet.context parentAvailable selected ambient assignment
      (assignment uv) accepted inheritedModel
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet bounded known
    parentEntry storedEdges depth free parentAvailable edge selected
  have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have actualCost : edgeCost scs before.core.counter edge =
      SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
    simp only [edgeCost, allowed, ↓reduceIte, projected]
  have actualReserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [actualCost] using reserved.edge costBound
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  have avoids := ready.avoids handle scs stored
  obtain ⟨r, n, p, h, k, actualCaller, middle, actualSaved, _final, _next, afterRoots, edgeResult,
    ⟨edgeRun, _post, _querySame, _growth, middlePaths, middleStorage, middleRealized, middleCounts,
    middleFlags, _origin, _retained, protects, _pendingHistory, _incomingHistory, shape,
    _returnedFits, _returnedKnown, _edgeAccepting⟩, edgeAccepting⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources_origins seed formulas solver
      inventory caller before checkEmpty parentEntry storedEdges depth free edge scs roots memos packet.context
      parentAvailable parentClosed selected ready.safe realized paths counts flags bucketBound pending
      allowed tries residual projected bounded actualReserved known
  obtain ⟨terms, termShape, childrenAccepted, guardHolds⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv)).mp accepted
  obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, middleSatisfied, middleOrigins⟩ :=
    edgeAccepting ambient assignment terms whole satisfied childrenAccepted
      (by simpa only [termShape] using guardHolds)
      (by simpa only [termShape] using inheritedModel) origins
      (by simpa only [termShape] using origins uv ready.inside)
  rcases shape with ⟨built, builtComplete, _middleSafe, fragmentBound, _fragmentPending, _fragmentSeparate⟩ |
    ⟨_fragments, _outer, _waiting, stopped⟩
  · have sameFragment : built = fragment :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj (builtComplete.symm.trans completed)).1
    subst built
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨fuel, after, finishRun, _raw, written, _finalStored, _finalFlag, _finalWaiting,
      _afterPaths, _afterCounts, _afterFlags, _afterStorage, _afterRealized, _afterSafe⟩ :=
      SourcePruningEnumerationFinalize.complete actualCaller.checked.native.machine.heap middle uv fragment
        (.unenumerated (some handle) scs) currentStored afterRoots middlePaths middleCounts middleFlags
        middleStorage fragmentBound middleRealized
    let padding := r + n + p + h + k + fuel
    let work := bound + padding
    have rl : r ≤ work := by dsimp [work, padding]; omega
    have nl : n ≤ work := by dsimp [work, padding]; omega
    have pl : p ≤ work := by dsimp [work, padding]; omega
    have hl : h ≤ work := by dsimp [work, padding]; omega
    have kl : k ≤ work := by dsimp [work, padding]; omega
    have fl : fuel ≤ work := by dsimp [work, padding]; omega
    have selectedAt := edgeRun (work - r) (work - n) work work (work - k) pl hl
    simp only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl, builtComplete] at selectedAt
    have finalizedAt := finishRun (work - fuel)
    simp only [Nat.add_sub_of_le fl] at finalizedAt
    have capturedAt : SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work
        uv scs edge caller before memos.query = some (.complete fragment actualCaller actualSaved after) := by
      simp only [SourcePruningEnumerationCapturedEdge.run, selectedAt, finalizedAt, Option.map_some]
    have receiptSame : receipt = .complete fragment actualCaller actualSaved after :=
      Option.some.inj ((running padding).symm.trans capturedAt)
    have reached : advance receipt = some (middleCaller, saved) := by
      rcases headShape with ⟨unsupported, _allowed, _projected⟩ |
        ⟨_outcome, advanced, _callback, _resources, _captured⟩
      · rw [receiptSame] at unsupported
        cases unsupported
      · simpa only [headQueries] using advanced
    rw [receiptSame] at reached
    change some (actualCaller, actualSaved) = some (middleCaller, saved) at reached
    have sameEndpoint := Option.some.inj reached
    have sameCaller : actualCaller = middleCaller := congrArg Prod.fst sameEndpoint
    have sameQueries : actualSaved = saved := congrArg Prod.snd sameEndpoint
    have finalSatisfied : Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient actualCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        extended after.core := by
      have selfValue : Fragments.fill extended fragment = extended uv :=
        (filled.trans termShape.symm).trans (agree uv ready.inside).symm
      exact (SourcePruningEnumerationFinalize.written_semantics middle.core after.core uv fragment
        (List.getElem?_eq_some_iff.mp currentStored).1 written
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient actualCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) extended).mpr
        ⟨EnumerationFrame.neutralize_satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient actualCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended uv middle.core middleSatisfied, selfValue⟩
    refine ⟨extended, fragment, after, agree, originalSatisfied, ?_, filled.trans termShape.symm, ?_⟩
    · simpa only [sameCaller, sameQueries] using receiptSame
    · refine ⟨?_, ?_⟩
      · simpa only [sameCaller] using finalSatisfied
      · simpa only [written] using middleOrigins
  · rw [stopped] at completed
    cases completed

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
