import MicroCFTA.SourcePruningEnumerationSharedScanPreparedHead
import MicroCFTA.SourcePruningEnumerationSharedRecordedModelWork
import MicroCFTA.SourcePruningEnumerationSharedPreparedHookCertificates
import MicroCFTA.SourcePruningEnumerationPolicyOrigins
import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation

/-!
# The same reached ordinary head supplies its false recording restart

One actual finite prefix retains its full packet and original assignment.
Its reached head retains the same extended model and full global memo.
Original pending refutation transfers below the original captured counter.
One actual recording callback preserves work and supplies the false restart.
A common native stage fuel retains the exact selected-head stop wrappers.
This result does not prove that the earlier prefix or recursive call completes.
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


open EnumerationDriver EnumerationCompressionFrame EnumerationProgress
open SourcePruningRecordTypes
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted FragmentHistory)
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "CallbackResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)

/-- The same actual reached head retains its false callback, refutation and restart packet. -/
theorem witnessed_prefix_complete_resources_models_work_proper_restart
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
      (SourceEqualityPCSGuard.holds formulas solver) ambient chosen (assignment uv))
    (policies : SourcePruningTemplates.OriginPolicies templates whole)
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group) :
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
          SourcePruningEnumerationNativeWork.work initialBound before assignment ∧
    ∃ (callbackFuel : Nat) (recorded : Bool × Metadata Typing) (callbackCore : Core),
      (((Packet formulas solver next afterCaller final recorded.2 (EnumerationExpandableIndex.frame callbackCore after) ∧
      RenderStable after.core callbackCore ∧ Frame after.core callbackCore ∧
      recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
      recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
      Fits (advance (stage recursiveFuel seed capturedMass inherited index) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance (stage recursiveFuel seed capturedMass inherited index) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries)).1) afterCaller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)) after.core recorded callbackCore ∧
        ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) after.core) =
          [.ok (recorded, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
            stop order,
          continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment afterCaller final.query after =
            if recorded.1 then .complete [] afterCaller final.query
            else recur recorded.2 afterCaller final.query (EnumerationExpandableIndex.frame callbackCore after)
              (SourcePruningEnumerationRestart.decision stop order recorded.2
                (EnumerationExpandableIndex.frame callbackCore after))) ∧
      ProperState callbackCore ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended callbackCore ∧
      AssignmentOrigins whole callbackCore.counter extended ∧
      (∀ (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat),
        SourcePruningEnumerationRestart.decision stop order recorded.2
          (EnumerationExpandableIndex.frame callbackCore after) ≠ some .stuck) ∧
      (templates = [] → recorded.1 = false) ∧
      (uv < after.core.counter → Fragments.fill extended fragment = extended uv →
        SourcePruningTemplates.OriginPolicies templates whole →
        (∀ group ∈ metadata.pending, Refutes extended group) →
        recorded.1 = false ∧ ∀ group ∈ recorded.2.pending, Refutes extended group)) ∧
      EnumerationStorageProgress.pendingSize callbackCore extended =
        EnumerationStorageProgress.pendingSize after.core extended ∧
      ∀ initialBound,
        SourcePruningEnumerationNativeWork.work initialBound (EnumerationExpandableIndex.frame callbackCore after) extended =
          SourcePruningEnumerationNativeWork.work initialBound after extended) ∧
      recorded.1 = false ∧
      (∀ group ∈ recorded.2.pending, Refutes extended group) ∧
      (∀ extra (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
          stop order,
        continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment afterCaller savedQueries after =
          recur recorded.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore after)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore after))) ∧
      EnumerationStorageProgress.pendingSize callbackCore extended + 1 ≤
        EnumerationStorageProgress.pendingSize before.core assignment ∧
      SourcePruningEnumerationNativeWork.work initialBound (EnumerationExpandableIndex.frame callbackCore after) extended <
        SourcePruningEnumerationNativeWork.work initialBound before assignment ∧
      ∃ stageFuel, ∀ extra,
        let w := stageFuel + extra
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
            graph templates stop order w metadata uv)
          checkEmpty w w w w w uv scs before (selectedEdges.take index) caller memos.query =
            .complete processed outputs prefixCaller prefixMemos.query ∧
        headRun checkEmpty w w w w w uv scs chosen prefixCaller before prefixMemos.query = some result ∧
        ExceptT.run (recordTypes graph templates w metadata uv (.inl fragment) after.core) =
          [.ok (recorded, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
            stop order,
          continueWith recur graph templates stop order w metadata uv fragment afterCaller savedQueries after =
            recur recorded.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore after)
              (SourcePruningEnumerationRestart.decision stop order recorded.2
                (EnumerationExpandableIndex.frame callbackCore after)) ∧
          SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
            (continueWith recur graph templates stop order w metadata uv)
            checkEmpty w w w w w uv scs before [chosen] prefixCaller prefixMemos.query =
            SourcePruningEnumerationSharedReceiptContinuation.run
              (fun _ _ _ _ => recur recorded.2 afterCaller savedQueries
                (EnumerationExpandableIndex.frame callbackCore after)
                (SourcePruningEnumerationRestart.decision stop order recorded.2
                  (EnumerationExpandableIndex.frame callbackCore after)))
              prefixCaller prefixMemos.query (some result) ∧
          SourcePruningEnumerationSharedPreparedRecursive.finish uv
            (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
              (continueWith recur graph templates stop order w metadata uv)
              checkEmpty w w w w w uv scs before [chosen] prefixCaller prefixMemos.query) =
            SourcePruningEnumerationSharedPreparedRecursive.finish uv
              (SourcePruningEnumerationSharedReceiptContinuation.run
                (fun _ _ _ _ => recur recorded.2 afterCaller savedQueries
                  (EnumerationExpandableIndex.frame callbackCore after)
                  (SourcePruningEnumerationRestart.decision stop order recorded.2
                    (EnumerationExpandableIndex.frame callbackCore after)))
                prefixCaller prefixMemos.query (some result))) ∧
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
  obtain ⟨bound, processed, outputs, prefixCaller, prefixNext, prefixMemos, prefixResult,
    prefixFull, appended, heads⟩ :=
    witnessed_prefix_complete_resources_models_work_proper
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges
      depth free packet ready stored parentAvailable parentClosed selected incoming bounded known
      selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved ambient
      assignment satisfied index chosen selectedAt proper whole origins initialBound currentBound accepted
  refine ⟨bound, processed, outputs, prefixCaller, prefixNext, prefixMemos, prefixResult,
    prefixFull, appended, ?_⟩
  intro prefixComplete
  obtain ⟨tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
    final, next, afterRoots, result, headFull, originalPost, commonBound, commonRunning⟩ := heads prefixComplete
  rcases headFull with ⟨coupled, afterProper, notStuck⟩
  rcases coupled with ⟨resource, fragment, extended, completed, agree, inputModel, outputModel,
    filledOriginal, filled, afterOrigins, inheritedHolds, decreased, workDecreased⟩
  have fullResource := resource
  rcases resource with ⟨_headRunning, headPost, querySame, growth, paths, storage, realized,
    counts, flags, _origin, _inputs, _protects, pendingTransfer, shape, headFits, headKnown⟩
  have completeShape : Safe after.core ∧ FragmentBound after.core.counter fragment ∧
      after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
      IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
      ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
    rw [completed] at shape
    rcases shape with ⟨otherFragment, same, safe, allocated, written, cleared, root, pendingFragment, ordered⟩ |
      ⟨_fragments, _outer, _waiting, stopped⟩
    · have sameFragment : otherFragment = fragment :=
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete.inj same).1.symm
      subst otherFragment
      exact ⟨safe, allocated, written, cleared, root, pendingFragment, ordered⟩
    · cases stopped
  rcases completeShape with ⟨afterSafe, allocated, written, cleared, root, pendingFragment, orderedGain⟩
  have captured := prefixFull.2.2.1
  have afterValid : SourcePruningEnumerationNativeBranchCompletion.CacheValid afterCaller after :=
    ⟨afterRoots, paths, storage, realized, counts, flags⟩
  have admitted : Admitted uv (.complete fragment afterCaller final.query after) :=
    ⟨afterValid, afterSafe, allocated, written, cleared, root⟩
  have history : FragmentHistory before.core (.complete fragment afterCaller final.query after) :=
    ⟨growth, pendingFragment, orderedGain⟩
  have pending := pendingTransfer captured.pending incoming
  obtain ⟨level, frontier, ordered⟩ := captured.ordered
  have headPacket := SourcePruningEnumerationSharedPreparedRecursive.receipt_packet
    formulas solver next afterCaller final metadata before.core uv fragment after level frontier
    headPost.context admitted history pending ordered captured.bounded
  have headRefuted := SourcePruningRecordTypes.pending_refutes_extension
    before.core.counter assignment extended metadata captured.bounded agree refuted
  have inside : uv < after.core.counter := Nat.lt_of_lt_of_le ready.inside growth
  obtain ⟨callbackFuel, recorded, callbackCore, callbackRetained, callbackPending, callbackWork⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources_models_work
      formulas solver next graph templates metadata uv fragment afterCaller final after
      (advance (stage recursiveFuel seed capturedMass inherited index)
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost chosen scs before.core.counter tries))
      headPacket allocated headFits headKnown afterProper ambient
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended whole outputModel afterOrigins
  have callbackFull := And.intro callbackRetained (And.intro callbackPending callbackWork)
  rcases callbackRetained with ⟨callbackResource, _callbackProper, _callbackModel,
    _callbackOrigins, _callbackNotStuck, _empty, compatible⟩
  obtain ⟨verdict, nextRefuted⟩ := compatible inside filled policies headRefuted
  rcases callbackResource with ⟨_callbackPacket, _stable, _frame, _types, _holes, _typing,
    _fits, _known, callbackRunning⟩
  have restart (extra : Nat)
      (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
      (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat) :
      continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment afterCaller savedQueries after =
        recur recorded.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore after)
          (SourcePruningEnumerationRestart.decision stop order recorded.2
            (EnumerationExpandableIndex.frame callbackCore after)) := by
    have actual := (callbackRunning extra).2.2 recur stop order
    simpa only [querySame, verdict, Bool.false_eq_true, ↓reduceIte] using actual
  refine ⟨tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
    final, next, afterRoots, result,
    ⟨⟨fullResource, fragment, extended, completed, agree, inputModel, outputModel,
      filledOriginal, filled, afterOrigins, inheritedHolds, decreased, workDecreased, ?_⟩,
      afterProper, notStuck⟩, originalPost, commonBound, commonRunning⟩
  refine ⟨callbackFuel, recorded, callbackCore, callbackFull, verdict, nextRefuted, restart, ?_, ?_, ?_⟩
  · rw [callbackPending]
    exact decreased
  · rw [callbackWork initialBound]
    exact workDecreased
  · let stageFuel := commonBound + callbackFuel
    refine ⟨stageFuel, ?_⟩
    intro extra
    dsimp only
    have commonEnough : commonBound ≤ stageFuel + extra := by dsimp only [stageFuel]; omega
    have callbackEnough : callbackFuel ≤ stageFuel + extra := by dsimp only [stageFuel]; omega
    have stageAt := commonRunning (stageFuel + extra - commonBound)
    simp only [Nat.add_sub_of_le commonEnough] at stageAt
    have callbackAt := callbackRunning (stageFuel + extra - callbackFuel)
    simp only [Nat.add_sub_of_le callbackEnough] at callbackAt
    refine ⟨stageAt.1, stageAt.2, callbackAt.2.1, ?_⟩
    intro recur stop order
    have restartAt := restart (stageFuel + extra - callbackFuel) recur stop order
    simp only [Nat.add_sub_of_le callbackEnough] at restartAt
    have headAt := stageAt.2
    rw [completed] at headAt
    have single :
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
          (continueWith recur graph templates stop order (stageFuel + extra) metadata uv)
          checkEmpty (stageFuel + extra) (stageFuel + extra) (stageFuel + extra) (stageFuel + extra) (stageFuel + extra)
          uv scs before [chosen] prefixCaller prefixMemos.query =
        SourcePruningEnumerationSharedReceiptContinuation.run
          (fun _ _ _ _ => recur recorded.2 afterCaller savedQueries
            (EnumerationExpandableIndex.frame callbackCore after)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore after)))
          prefixCaller prefixMemos.query (some result) := by
      simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run, headAt,
        SourcePruningEnumerationSharedReceiptContinuation.run, completed, restartAt, List.append_nil]
      generalize actualRecur : recur recorded.2 afterCaller savedQueries
        (EnumerationExpandableIndex.frame callbackCore after)
        (SourcePruningEnumerationRestart.decision stop order recorded.2
          (EnumerationExpandableIndex.frame callbackCore after)) = resumed
      cases resumed <;> rfl
    exact ⟨restartAt, single, congrArg (SourcePruningEnumerationSharedPreparedRecursive.finish uv) single⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
