import MicroCFTA.SourcePruningEnumerationSharedScanModels
import MicroCFTA.SourcePruningEnumerationSharedCapturedProgressWork
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
import MicroCFTA.SourcePruningEnumerationSharedRecursiveReservationBounds

/-!
# One witnessed head after its actual finite sibling prefix

The finite prefix retains its full packet and the original assignment.
A completed prefix supplies the next head's actual caller and full memo.
A stopped prefix retains its exact outputs and optional endpoint.
One reached head supplies the same resource, model, work and properness packet.
This result does not prove that earlier hooks or recursive calls complete.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedPreparedReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure continueWith resume endpoint)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "headRun" => SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
local notation "advance" => SourcePruningEnumerationSharedIncomingReservation.advance
open SourcePruningEnumerationOrigins
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]


/-- The actual finite prefix supplies the witnessed head at its same completed endpoint. -/
theorem witnessed_prefix_complete_resources_models_work_proper
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
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
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (index : Nat) (chosen : EdgeValue Symbol Constraint)
    (selectedAt : selectedEdges[index]? = some chosen)
    (proper : EnumerationProgress.ProperState before.core)
    (whole : Term Symbol) (origins : AssignmentOrigins whole before.core.counter assignment)
    (initialBound : Nat)
    (currentBound : EnumerationStorageProgress.pendingSize before.core assignment ≤ initialBound)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient chosen (assignment uv)) :
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (prefixCaller : Caller (bits + 2)) (prefixNext : Inventory) (prefixMemos : Memos)
      (prefixResult : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before (selectedEdges.take index) caller memos.query = prefixResult) ∧
      Post formulas solver prefixNext caller prefixCaller prefixMemos ∧
      Packet formulas solver prefixNext prefixCaller prefixMemos metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited (selectedEdges.take index).length).2 prefixCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited (selectedEdges.take index).length).1)
        prefixCaller.checked.native.machine.heap ∧
      processed.length ≤ (selectedEdges.take index).length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ position, position < (selectedEdges.take index).length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited position output) ∧
      (prefixResult = .complete processed outputs prefixCaller prefixMemos.query ∨
        ∃ current, prefixResult = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (prefixCaller, prefixMemos.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient prefixCaller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        assignment before.core) ∧
      (∀ extra,
        let w := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
          graph templates stop order w metadata uv
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty w w w w w
          uv scs before selectedEdges caller memos.query =
        match prefixResult with
        | .stopped earlier outputs current => .stopped earlier outputs current
        | .complete earlier outputs reached saved =>
            match SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty w w w w w
              uv scs before (chosen :: selectedEdges.drop (index + 1)) reached saved with
            | .complete later more finalCaller finalQueries =>
                .complete (earlier ++ later) (outputs ++ more) finalCaller finalQueries
            | .stopped later more current => .stopped (earlier ++ later) (outputs ++ more) current) ∧
      (prefixResult = .complete processed outputs prefixCaller prefixMemos.query →
        ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
          SourcePruningEnumerationConstraint.project chosen.entry.key.constraint = some (tries, residual) ∧
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Receipt (bits + 2)),
      ((((∀ er en P H ek, p ≤ P → h ≤ H →
        headRun checkEmpty (r + er) (n + en) P H (k + ek) uv scs chosen prefixCaller before prefixMemos.query = some result) ∧
      Post formulas solver next prefixCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance (stage recursiveFuel seed capturedMass inherited index) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance (stage recursiveFuel seed capturedMass inherited index)
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap) ∧
      ∃ (fragment : Fragment) (extended : Nat → Term Symbol),
        result = .complete fragment afterCaller savedQueries after ∧
        (∀ held < before.core.counter, extended held = assignment held) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient prefixCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended before.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core ∧
        Fragments.fill extended fragment = assignment uv ∧
        Fragments.fill extended fragment = extended uv ∧
        AssignmentOrigins whole after.core.counter extended ∧
        (∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
        EnumerationStorageProgress.pendingSize after.core extended + 1 ≤
          EnumerationStorageProgress.pendingSize before.core assignment ∧
        SourcePruningEnumerationNativeWork.work initialBound after extended <
          SourcePruningEnumerationNativeWork.work initialBound before assignment) ∧
      EnumerationProgress.ProperState after.core ∧
      ∀ (Typing : Type)
        (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
        (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
        (metadata : SourcePruningRecordTypes.Metadata Typing),
        SourcePruningEnumerationRestart.decision stop order metadata after ≠ some .stuck) ∧
        Post formulas solver next caller afterCaller final ∧
        ∃ commonFuel, ∀ extra,
          let w := commonFuel + extra
          SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
              graph templates stop order w metadata uv)
            checkEmpty w w w w w uv scs before (selectedEdges.take index) caller memos.query =
              .complete processed outputs prefixCaller prefixMemos.query ∧
          headRun checkEmpty w w w w w uv scs chosen prefixCaller before prefixMemos.query = some result) := by
  obtain ⟨inside, chosenAt⟩ := List.getElem_of_getElem? selectedAt
  have prefixLength : (selectedEdges.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt inside)
  have decomposed : selectedEdges.take index ++ chosen :: selectedEdges.drop (index + 1) = selectedEdges := by
    rw [← chosenAt, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  have prefixSelected : ∀ edge ∈ selectedEdges.take index, edge ∈ storedEdges := by
    intro edge member
    exact selected edge (List.mem_of_mem_take member)
  have prefixReservation := reserved.prefix (List.length_take_le' index selectedEdges)
  obtain ⟨bound, processed, outputs, prefixCaller, prefixNext, prefixMemos, prefixResult,
    running, prefixPost, captured, prefixFits, prefixKnown, processedLength, receipts, outputPackets,
    shape, sameModel⟩ :=
    alternatives_finite_complete_resources_models
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges
      (selectedEdges.take index) depth free packet ready stored parentAvailable parentClosed
      prefixSelected incoming bounded known selectionMembers selectionLength capturedMass inherited
      initialMass inheritedLength prefixReservation ambient assignment satisfied
  refine ⟨bound, processed, outputs, prefixCaller, prefixNext, prefixMemos, prefixResult,
    ⟨running, prefixPost, captured, prefixFits, prefixKnown, processedLength, receipts, outputPackets,
      shape, sameModel⟩, ?_, ?_⟩
  · intro extra
    dsimp only
    have appended := SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run_append
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
      checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      uv scs before (selectedEdges.take index) (chosen :: selectedEdges.drop (index + 1)) caller memos.query
    rw [running extra, decomposed] at appended
    cases prefixResult with
    | stopped _ _ _ => exact appended
    | complete _ _ reached saved =>
        dsimp only at appended ⊢
        generalize actualSuffix : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv scs before (chosen :: selectedEdges.drop (index + 1)) reached saved = suffix at appended ⊢
        cases suffix <;> exact appended
  · intro prefixComplete
    let currentSeed := stage recursiveFuel seed capturedMass inherited index
    have currentFits : Fits currentSeed.2 prefixCaller.checked := by
      simpa only [currentSeed, prefixLength] using prefixFits
    have currentKnown : Heap (fun guard => guard ∈ currentSeed.1) prefixCaller.checked.native.machine.heap := by
      simpa only [currentSeed, prefixLength] using prefixKnown
    have currentAvailable := prefixPost.effects.keeps.available
      (.node parentEntry storedEdges depth free) parentAvailable
    have chosenMember : chosen ∈ storedEdges := selected chosen (List.mem_of_getElem? selectedAt)
    have slotModel := EnumerationCompleteness.stored_satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient prefixCaller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core sameModel uv (.unenumerated (some handle) scs) stored
    simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at slotModel
    obtain ⟨tries, residual, _terms, projected, _valid, _shape, _children, _length,
      allowed, _ownEqualities, _residualHeld⟩ :=
      SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver prefixNext
        prefixCaller prefixMemos parentEntry storedEdges depth free chosen scs prefixPost.context
        currentAvailable chosenMember ambient assignment (assignment uv) accepted slotModel.2
    have counted : ScanReserved bits recursiveFuel seed capturedMass inherited
        (index + (selectedEdges.length - index)) := by
      rw [Nat.add_sub_of_le (Nat.le_of_lt inside)]
      exact reserved
    have remaining := SourcePruningEnumerationSharedPreparedReservation.ScanReserved.after_prefix
      (consumed := index) (remaining := selectedEdges.length - index) counted
    have remainingLength : selectedEdges.length - index = (selectedEdges.length - (index + 1)) + 1 := by omega
    rw [remainingLength] at remaining
    have headReservation := remaining.head
    obtain ⟨childrenBound, ownBound⟩ :=
      SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet currentSeed formulas solver prefixNext
        prefixCaller prefixMemos metadata before captured currentFits currentKnown
        parentEntry storedEdges depth free currentAvailable chosen chosenMember
    have costBound := SourcePruningEnumerationSharedRecursiveReservation.edge_cost_le currentSeed inherited scs
      before.core.counter chosen childrenBound ownBound inheritedLength
    have exactCost : SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost scs before.core.counter chosen =
        SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries := by
      simp only [SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost, allowed, ↓reduceIte, projected]
    have edgeReservation : SourcePruningEnumerationSharedIncomingReservation.Reserved bits currentSeed
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries) := by
      rw [← exactCost]
      exact headReservation.edge costBound
    obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := captured.valid
    have pending := EnumerationReferences.pending_inputs before.core captured.pending uv (some handle) scs stored
    obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
      coupled, afterProper, notStuck⟩ :=
      SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.complete_models_resources_work_proper_progress_prepared
        currentSeed formulas solver prefixNext prefixCaller before checkEmpty uv handle scs
        parentEntry storedEdges depth free chosen roots prefixMemos prefixPost.context ready stored
        currentAvailable parentClosed realized chosenMember paths counts flags pending tries residual projected
        currentFits edgeReservation currentKnown ambient assignment whole sameModel accepted origins
        initialBound currentBound proper
    have originalPost := prefixPost.trans coupled.1.2.1
    refine ⟨tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
      final, next, afterRoots, result, ⟨coupled, afterProper, notStuck⟩, originalPost, ?_⟩
    let commonFuel := bound + r + n + p + h + k
    refine ⟨commonFuel, ?_⟩
    intro extra
    dsimp only
    have prefixEnough : bound ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have rEnough : r ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have nEnough : n ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have pEnough : p ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have hEnough : h ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have kEnough : k ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
    have prefixAt := running (commonFuel + extra - bound)
    simp only [Nat.add_sub_of_le prefixEnough] at prefixAt
    have headAt := coupled.1.1 (commonFuel + extra - r) (commonFuel + extra - n)
      (commonFuel + extra) (commonFuel + extra) (commonFuel + extra - k) pEnough hEnough
    simp only [Nat.add_sub_of_le rEnough, Nat.add_sub_of_le nEnough, Nat.add_sub_of_le kEnough] at headAt
    exact ⟨prefixAt.trans prefixComplete, headAt⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
