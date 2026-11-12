import MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedRestart
import MicroCFTA.SourcePruningEnumerationSharedPrefixStableWork

/-!
# One adequate common stage fuel for an opaque restart

One stable prefix observation retains the full policy packet.
The same preparation, opaque head and callback use one sufficient native fuel.
The prepared action may vary. Its actual prefix execution stays fixed.
The result preserves the actual continuation and recursive stop wrappers.
This result does not prove completion of the recursive call or ordinary scan.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCommonOpaqueRestart
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
open SourcePruningEnumerationSharedRecursiveReservation (narrowSeed)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationOrigins
open EnumerationStorageProgress
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advanceCaller" => SourcePruningEnumerationSelectedValueCaller.advance
local notation "advance" => SourcePruningEnumerationSharedIncomingReservation.advance
local notation "run" => SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
local notation "edgesOf" => InternedEdgeResidency.nodeEdges
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

open EnumerationDriver EnumerationCompressionFrame EnumerationProgress
open SourcePruningRecordTypes
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure continueWith)
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "CallbackResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)

/-- One fixed current tuple admits the same stage observations at every larger native fuel. -/
def CommonOpaqueRestart
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (checkEmpty : Bool)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (uv handle : Nat)
    (caller reached : Caller (bits + 2)) (before narrowed : Cached) (queries prefixQueries : Queries)
    (scs : List Suspended) (decoded prepared : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached)
    (receipt : Result (bits + 2)) (fragment : Fragment) (headCaller : Caller (bits + 2))
    (headQueries : Queries) (after : Cached) (recorded : Bool × Metadata Typing) (callbackCore : Core) : Prop :=
  ∃ (workFuel : Nat) (checked : Core) (value : Node)
      (prefixHeap : InternedConstructorTemplates.State Symbol Constraint),
    ∀ extra,
      let w := workFuel + extra
      ∃ action : EnumerateM Symbol Constraint Unit,
        runPrefix holeKey fits admits graph templates stop order metadata w w w w w w uv caller before queries =
          .narrowed checked (.done (value, some action) prefixHeap) reached prefixQueries
            (some [.ok ((), narrowed.core)]) (some narrowed)
            (some [.ok ((false, metadata), narrowed.core)]) none ∧
        SourcePruningEnumerationSelectedPreparation.run w w uv reached narrowed =
          ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)) ∧
        SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty w w w w w uv scs prepared
          (advanceCaller reached heap) entered prefixQueries = some receipt ∧
        ExceptT.run (recordTypes graph templates w metadata uv (.inl fragment) after.core) =
          [.ok (recorded, callbackCore)] ∧
        (∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult),
          continueWith recur graph templates stop order w metadata uv fragment headCaller headQueries after =
            recur recorded.2 headCaller headQueries (EnumerationExpandableIndex.frame callbackCore after)
              (SourcePruningEnumerationRestart.decision stop order recorded.2
                (EnumerationExpandableIndex.frame callbackCore after))) ∧
        (∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult),
          SourcePruningEnumerationSharedPreparedContinuations.run
            (continueWith recur graph templates stop order w metadata uv)
            checkEmpty w w w w w w w uv edgesOf reached narrowed prefixQueries =
          (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)),
            some (SourcePruningEnumerationSharedReceiptContinuation.run
              (fun _ _ _ _ => recur recorded.2 headCaller headQueries
                (EnumerationExpandableIndex.frame callbackCore after)
                (SourcePruningEnumerationRestart.decision stop order recorded.2
                  (EnumerationExpandableIndex.frame callbackCore after)))
              (advanceCaller reached heap) prefixQueries (some receipt)))) ∧
        ∀ depth,
          SourcePruningEnumerationSharedPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
            stop order w (depth + 1) metadata caller queries before (some (.expand uv)) =
          SourcePruningEnumerationSharedPreparedRecursive.finish uv
            (SourcePruningEnumerationSharedReceiptContinuation.run
              (fun _ _ _ _ =>
                SourcePruningEnumerationSharedPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                  stop order w depth recorded.2 headCaller headQueries
                  (EnumerationExpandableIndex.frame callbackCore after)
                  (SourcePruningEnumerationRestart.decision stop order recorded.2
                    (EnumerationExpandableIndex.frame callbackCore after)))
              (advanceCaller reached heap) prefixQueries (some receipt))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem entered_frame (before after : Cached)
    (flags : after.expandable = before.expandable) (waiting : after.waiting = before.waiting) :
    EnumerationExpandableIndex.frame after.core before = after := by
  cases before
  cases after
  dsimp only [EnumerationExpandableIndex.frame] at flags waiting ⊢
  cases flags
  cases waiting
  rfl

private theorem adequate_of_stable
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (checkEmpty : Bool)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (uv handle prefixFuel preparationFuel headFuel callbackFuel : Nat)
    (caller reached : Caller (bits + 2)) (before narrowed : Cached) (queries prefixQueries : Queries)
    (scs : List Suspended) (decoded prepared : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached)
    (receipt : Result (bits + 2)) (fragment : Fragment) (headCaller : Caller (bits + 2))
    (headQueries : Queries) (after : Cached) (recorded : Bool × Metadata Typing) (callbackCore : Core)
    (checked : Core) (value : Node) (prefixHeap : InternedConstructorTemplates.State Symbol Constraint)
    (prefixStable : ∀ extra, ∃ action : EnumerateM Symbol Constraint Unit,
      runPrefix holeKey fits admits graph templates stop order metadata
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before queries =
        .narrowed checked (.done (value, some action) prefixHeap) reached prefixQueries
          (some [.ok ((), narrowed.core)]) (some narrowed)
          (some [.ok ((false, metadata), narrowed.core)]) none)
    (preparation : ∀ extra, SourcePruningEnumerationSelectedPreparation.run
      (preparationFuel + extra) (preparationFuel + extra) uv reached narrowed =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)))
    (sameFrame : EnumerationExpandableIndex.frame entered.core narrowed = entered)
    (boundary : MergedOrdinaryHeight.recursiveBoundary prepared = true)
    (head : ∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
      (headFuel + extra) (headFuel + extra) (headFuel + extra) (headFuel + extra) (headFuel + extra)
      uv scs prepared (advanceCaller reached heap) entered prefixQueries = some receipt)
    (completed : receipt = .complete fragment headCaller headQueries after)
    (callback : ∀ extra, ExceptT.run
      (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) after.core) =
        [.ok (recorded, callbackCore)])
    (restart : ∀ extra
      (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult),
      continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment headCaller headQueries after =
        recur recorded.2 headCaller headQueries (EnumerationExpandableIndex.frame callbackCore after)
          (SourcePruningEnumerationRestart.decision stop order recorded.2
            (EnumerationExpandableIndex.frame callbackCore after))) :
    CommonOpaqueRestart holeKey fits admits graph templates checkEmpty stop order metadata uv handle
      caller reached before narrowed queries prefixQueries scs decoded prepared heap entered
      receipt fragment headCaller headQueries after recorded callbackCore := by
  let commonFuel := prefixFuel + preparationFuel + headFuel + callbackFuel
  refine ⟨commonFuel, checked, value, prefixHeap, ?_⟩
  intro extra
  dsimp only
  have pEnough : prefixFuel ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
  have dEnough : preparationFuel ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
  have hEnough : headFuel ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
  have cEnough : callbackFuel ≤ commonFuel + extra := by dsimp only [commonFuel]; omega
  obtain ⟨action, actualPrefix⟩ := prefixStable (commonFuel + extra - prefixFuel)
  have prefixAt := actualPrefix
  simp only [Nat.add_sub_of_le pEnough] at prefixAt
  have preparationAt := preparation (commonFuel + extra - preparationFuel)
  simp only [Nat.add_sub_of_le dEnough] at preparationAt
  have headAt := head (commonFuel + extra - headFuel)
  simp only [Nat.add_sub_of_le hEnough] at headAt
  have callbackAt := callback (commonFuel + extra - callbackFuel)
  simp only [Nat.add_sub_of_le cEnough] at callbackAt
  have restartAt (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult) :=
    restart (commonFuel + extra - callbackFuel) recur
  simp only [Nat.add_sub_of_le cEnough] at restartAt
  have preparedAt (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult) :
      SourcePruningEnumerationSharedPreparedContinuations.run
        (continueWith recur graph templates stop order (commonFuel + extra) metadata uv)
        checkEmpty (commonFuel + extra) (commonFuel + extra) (commonFuel + extra)
          (commonFuel + extra) (commonFuel + extra) (commonFuel + extra) (commonFuel + extra)
          uv edgesOf reached narrowed prefixQueries =
      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run
          (fun _ _ _ _ => recur recorded.2 headCaller headQueries
            (EnumerationExpandableIndex.frame callbackCore after)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore after)))
          (advanceCaller reached heap) prefixQueries (some receipt))) := by
    have routed :
        SourcePruningEnumerationSharedPreparedContinuations.run
          (continueWith recur graph templates stop order (commonFuel + extra) metadata uv)
          checkEmpty (commonFuel + extra) (commonFuel + extra) (commonFuel + extra)
            (commonFuel + extra) (commonFuel + extra) (commonFuel + extra) (commonFuel + extra)
            uv edgesOf reached narrowed prefixQueries =
        (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)),
          some (SourcePruningEnumerationSharedReceiptContinuation.run
            (continueWith recur graph templates stop order (commonFuel + extra) metadata uv)
            (advanceCaller reached heap) prefixQueries (some receipt))) := by
      simp only [SourcePruningEnumerationSharedPreparedContinuations.run, preparationAt, sameFrame]
      cases prepared <;> simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
      all_goals simp only [headAt, ite_self]
    rw [routed, completed]
    simp only [SourcePruningEnumerationSharedReceiptContinuation.run, restartAt]
  refine ⟨action, prefixAt, preparationAt, headAt, callbackAt, restartAt, preparedAt, ?_⟩
  intro depth
  have actual := SourcePruningEnumerationSharedPreparedRecursive.resume_prepared
    holeKey fits admits graph templates checkEmpty edgesOf stop order (commonFuel + extra) depth uv
    metadata metadata caller reached queries prefixQueries before narrowed checked narrowed.core
    (.done (value, some action) prefixHeap) narrowed.core prefixAt
  simpa only [preparedAt] using actual

/-- One retained policy packet supplies an adequate common fuel for its actual opaque restart. -/
theorem complete_models_resources_work_restart_common
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool)
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (proper : EnumerationProgress.ProperState before.core)
    (uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ceiling : Nat)
    (bucketBound : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits 1 seed ceiling)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (initialBound : Nat)
    (currentBound : EnumerationStorageProgress.pendingSize before.core assignment ≤ initialBound)
    (unary : ∀ symbol annotation child, assignment uv = .node symbol [child] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
      admits (holeKey metadata.typing uv) annotation = true ∧ fits (holeKey metadata.typing uv) symbol = true)
    (application : ∀ annotation first second third fourth,
      assignment uv = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true)
    (filtered : ∀ annotation first second,
      assignment uv = .node ("filter", FullSyntax.Formula.top) [first, second] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true)
    (policies : SourcePruningTemplates.OriginPolicies templates whole)
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group) :
    ∃ fuel, ∀ extra,
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before memos.query
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos observed ∧
      Resources seed.2 (fun guard => guard ∈ seed.1) caller observed ∧
      (match (generalizing := false) observed with
        | .parked _ (some after) _ =>
            pendingSize after.core assignment = pendingSize before.core assignment ∧
            (EnumerationIndexSelection.candidates after).length + 1 =
              (EnumerationIndexSelection.candidates before).length ∧
            SourcePruningEnumerationNativeWork.work initialBound after assignment + 1 =
              SourcePruningEnumerationNativeWork.work initialBound before assignment
        | .narrowed _ _ _ _ _ (some after) _ _ =>
            after.core.counter = before.core.counter ∧
            (∀ other, other ≠ uv → after.expandable other = before.expandable other) ∧
            pendingSize after.core assignment = pendingSize before.core assignment ∧
            (EnumerationIndexSelection.candidates after).length +
                (if after.expandable uv then 0 else 1) =
              (EnumerationIndexSelection.candidates before).length ∧
            SourcePruningEnumerationNativeWork.work initialBound after assignment +
                (if after.expandable uv then 0 else 1) =
              SourcePruningEnumerationNativeWork.work initialBound before assignment
        | _ => True) ∧
      match observed with
      | .parked _ (some after) _ =>
          Packet formulas solver inventory caller memos metadata after ∧
          EnumerationProgress.ProperState after.core ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
            assignment after.core ∧
          AssignmentOrigins whole after.core.counter assignment
      | .narrowed _ _ reached prefixQueries _ (some narrowedCache) _ _ =>
          ∃ (handle : Nat) (scs : List Suspended) (value : Node) (prefixMemos : Memos),
            (Post formulas solver inventory caller reached prefixMemos ∧ prefixMemos.query = prefixQueries ∧
            Packet formulas solver inventory reached prefixMemos metadata narrowedCache ∧
            EnumerationDriver.Ready uv narrowedCache.core ∧
            narrowedCache.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
            lookupNode reached.checked.native.machine.heap handle = some value ∧
            Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
            EnumerationReferences.IncomingAvoid uv narrowedCache.core ∧
            InputsPending narrowedCache.core scs ∧
            (∀ sc ∈ scs, sc.var < before.core.counter) ∧
            scs.length ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
            narrowedCache.core.counter = before.core.counter ∧ narrowedCache.waiting = before.waiting ∧
            Fits (narrowSeed seed).2 reached.checked ∧
            Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) ∧
            EnumerationProgress.ProperState narrowedCache.core ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient reached.checked.native.machine.heap)
              (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
              assignment narrowedCache.core ∧
            AssignmentOrigins whole narrowedCache.core.counter assignment ∧
            ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
              Post formulas solver inventory caller (advanceCaller reached heap) prefixMemos ∧
              (((∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra) uv reached narrowedCache =
                ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
              lookupNode reached.checked.native.machine.heap handle = some decoded ∧
              Post formulas solver inventory reached
                (SourcePruningEnumerationSelectedValueCaller.advance reached heap) prefixMemos ∧
              Packet formulas solver inventory
                (SourcePruningEnumerationSelectedValueCaller.advance reached heap) prefixMemos metadata entered ∧
              EnumerationDriver.RenderStable narrowedCache.core entered.core ∧
              EnumerationDriver.Ready uv entered.core ∧
              entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
              entered.core.counter = narrowedCache.core.counter ∧ entered.core.values = narrowedCache.core.values ∧
              entered.expandable = narrowedCache.expandable ∧ entered.waiting = narrowedCache.waiting ∧
              Available heap result ∧ result.free = [] ∧
              (∀ holds ambient term,
                InternedGuardedLanguage.meaning holds ambient result term ↔
                  InternedGuardedLanguage.meaning holds ambient decoded term) ∧
              ∀ holds ambient residualMeaning assignment,
                (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
                  residualMeaning assignment entered.core ↔
                Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
                  reached.checked.native.machine.heap) residualMeaning assignment narrowedCache.core) ∧
                (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
                  reached.checked.native.machine.heap) residualMeaning assignment narrowedCache.core →
                  InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
              SourceCurrentConstrainedCapGeneratedQueryResources.Fits
                (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (narrowSeed seed).2)
                (SourcePruningEnumerationSelectedValueCaller.advance reached heap).checked ∧
              InternedValueMass.value result ≤
                (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (narrowSeed seed).2).mass ∧
              InternedFreshOrdinaryConstraintHeap.Heap (fun guard => guard ∈ seed.1) heap) ∧
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient heap)
                (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                assignment entered.core ∧
              AssignmentOrigins whole entered.core.counter assignment ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                ambient result (assignment uv) ∧
              (∀ (entry : Cache.Interned InternedBinderProtocol.NodeKey)
                (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
                (free : List InternedBinderProtocol.Reference), result = .node entry rows depth free →
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
                ∃ (edge : EdgeValue Symbol Constraint),
                  edge ∈ SourceCurrentEnumerationOrder.internedEdgesOf InternedEdgeResidency.nodeEdges
                    decoded (.node entry rows depth free) ∧ edge ∈ rows ∧
                  InternedEdgeResidency.EdgeResident heap edge ∧
                  InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
                    ambient edge (assignment uv) ∧
                ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
                  SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
                  ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
              (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
              (Post formulas solver next caller afterCaller final ∧
              Post formulas solver next reached afterCaller final ∧
              ((∀ er en P H ek, p ≤ P → h ≤ H →
                run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge (advanceCaller reached heap) entered prefixMemos.query = some result) ∧
              Post formulas solver next (advanceCaller reached heap) afterCaller final ∧ final.query = savedQueries ∧
              entered.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
              StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
              EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
              (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
                ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
              (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
                entered.core.values[held]? = some (.enumerated fragment)) ∧
              InputsPending after.core scs ∧
              (∀ held, held ≠ uv → held < entered.core.counter → IsRoot entered.core.representatives held →
                Avoids entered.core.representatives held scs → EnumerationDriver.Protected held entered.core after.core) ∧
              (EnumerationReferences.PendingReferences entered.core → EnumerationReferences.IncomingAvoid uv entered.core →
                EnumerationReferences.PendingReferences after.core) ∧
              ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
                  Safe after.core ∧ FragmentBound after.core.counter fragment ∧
                  after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
                  IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
                  ∀ level frontier, EnumerationOrder.Stratified entered.core level frontier →
                    ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
                ∃ fragments outer waiting, result = .stopped fragments
                  (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
              Fits (advance (preparedSeed seed) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).2 afterCaller.checked ∧
              Heap (fun guard => guard ∈ (advance (preparedSeed seed)
                (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).1)
                afterCaller.checked.native.machine.heap) ∧
              ∃ (fragment : Fragment) (extended : Nat → Term Symbol),
                (result = .complete fragment afterCaller savedQueries after ∧
                (∀ held < entered.core.counter, extended held = assignment held) ∧
                Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                    ambient (advanceCaller reached heap).checked.native.machine.heap)
                  (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                  extended entered.core ∧
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
    ∃ (callbackFuel : Nat) (recorded : Bool × Metadata Typing) (callbackCore : Core),
      ((((Packet formulas solver next afterCaller final recorded.2 (EnumerationExpandableIndex.frame callbackCore after) ∧
      RenderStable after.core callbackCore ∧ Frame after.core callbackCore ∧
      recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
      recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
      Fits (advance (preparedSeed seed) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance (preparedSeed seed) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).1) afterCaller.checked.native.machine.heap ∧
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
      ∀ extra (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
          stop order,
        continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment afterCaller savedQueries after =
          recur recorded.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore after)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore after))) ∧
                pendingSize callbackCore extended + 1 ≤ pendingSize before.core assignment ∧
                SourcePruningEnumerationNativeWork.work initialBound
                  (EnumerationExpandableIndex.frame callbackCore after) extended <
                  SourcePruningEnumerationNativeWork.work initialBound before assignment) ∧
              EnumerationProgress.ProperState after.core ∧
              ∀ (NextTyping : Type)
                (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
                (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
                (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
                SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck) ∧
              (MergedOrdinaryHeight.recursiveBoundary result = true →
            ∃ (headBound : Nat) (receipt : Result (bits + 2)) (headCaller : Caller (bits + 2))
              (saved : Queries) (final : Memos) (next : Inventory),
              Post formulas solver next caller headCaller final ∧
              Post formulas solver next reached headCaller final ∧
              ((∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
                (headBound + extra) (headBound + extra) (headBound + extra) (headBound + extra) (headBound + extra)
                uv scs result (advanceCaller reached heap) entered prefixMemos.query = some receipt) ∧
              Post formulas solver next (advanceCaller reached heap) headCaller final ∧ final.query = saved ∧
              SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance receipt = some (headCaller, saved) ∧
              Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory entered.core receipt ∧
              Fits (advance (preparedSeed seed) (scs.length + 1)).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (advance (preparedSeed seed) (scs.length + 1)).1) headCaller.checked.native.machine.heap ∧
              ((∃ fragment after, receipt = .complete fragment headCaller saved after ∧
                  Packet formulas solver next headCaller final metadata after ∧
                  after.core.counter ≤ entered.core.counter + 1 ∧
                  SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core + scs.length) ∨
                (∃ after outer waiting, receipt = .stopped []
                  (.ok (some []), headCaller, saved, outer, waiting) (some after) ∧
                  after.core.counter ≤ entered.core.counter + 1 ∧
                  SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core + scs.length) ∨
                receipt = .rejected (advanceCaller reached heap) prefixMemos.query entered) ∧
              SourcePruningEnumerationSharedSelectedOpaqueDispatch.FinalizationAt checkEmpty headBound uv scs result (advanceCaller reached heap) entered prefixMemos.query receipt) ∧
              ∃ (fragment : Fragments.Fragment Symbol) (after : Cached) (extended : Nat → Term Symbol),
                ((receipt = .complete fragment headCaller saved after ∧
                extended = install assignment entered.core.counter [assignment uv] ∧
                (∀ held < entered.core.counter, extended held = assignment held) ∧
                Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                    ambient (advanceCaller reached heap).checked.native.machine.heap)
                  (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                  extended entered.core ∧
                Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                    ambient headCaller.checked.native.machine.heap)
                  (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                  extended after.core ∧
                Fragments.fill extended fragment = assignment uv ∧
                Fragments.fill extended fragment = extended uv ∧
                AssignmentOrigins whole after.core.counter extended ∧
                (∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
                EnumerationStorageProgress.pendingSize after.core extended = EnumerationStorageProgress.pendingSize entered.core assignment ∧
                (∀ headInitialBound, SourcePruningEnumerationNativeWork.work headInitialBound after extended +
                  (if entered.expandable uv then 1 else 0) =
                  SourcePruningEnumerationNativeWork.work headInitialBound entered assignment) ∧
                (EnumerationProgress.ProperState entered.core →
                  EnumerationProgress.ProperState after.core ∧
                  ∀ (NextTyping : Type)
                    (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
                    (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
                    (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
                    SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck)) ∧
                EnumerationStorageProgress.pendingSize after.core extended =
                  EnumerationStorageProgress.pendingSize before.core assignment ∧
                SourcePruningEnumerationNativeWork.work initialBound after extended + 1 =
                  SourcePruningEnumerationNativeWork.work initialBound before assignment ∧
                EnumerationProgress.ProperState after.core ∧
                ∀ (NextTyping : Type)
                  (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
                  (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
                  (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
                  SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck) ∧
    ∃ (callbackFuel : Nat) (recorded : Bool × Metadata Typing) (callbackCore : Core),
      ((((Packet formulas solver next headCaller final recorded.2 (EnumerationExpandableIndex.frame callbackCore after) ∧
      RenderStable after.core callbackCore ∧ Frame after.core callbackCore ∧
      recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
      recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
      Fits (advance (preparedSeed seed) (scs.length + 1)).2 headCaller.checked ∧
      Heap (fun guard => guard ∈ (advance (preparedSeed seed) (scs.length + 1)).1) headCaller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)) after.core recorded callbackCore ∧
        ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) after.core) =
          [.ok (recorded, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
            stop order,
          continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment headCaller final.query after =
            if recorded.1 then .complete [] headCaller final.query
            else recur recorded.2 headCaller final.query (EnumerationExpandableIndex.frame callbackCore after)
              (SourcePruningEnumerationRestart.decision stop order recorded.2
                (EnumerationExpandableIndex.frame callbackCore after))) ∧
      ProperState callbackCore ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient headCaller.checked.native.machine.heap) (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended callbackCore ∧
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
      ∀ extra (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
          stop order,
        continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment headCaller saved after =
          recur recorded.2 headCaller saved (EnumerationExpandableIndex.frame callbackCore after)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore after))) ∧
                pendingSize callbackCore extended = pendingSize before.core assignment ∧
                SourcePruningEnumerationNativeWork.work initialBound
                  (EnumerationExpandableIndex.frame callbackCore after) extended + 1 =
                  SourcePruningEnumerationNativeWork.work initialBound before assignment ∧
                CommonOpaqueRestart holeKey fits admits graph templates checkEmpty stop order metadata uv handle
                  caller reached before narrowedCache memos.query prefixQueries scs decoded result heap entered
                  receipt fragment headCaller saved after recorded callbackCore)
      | _ => False := by
  obtain ⟨policyFuel, policy⟩ :=
    SourcePruningEnumerationSharedPolicyPreparedRestart.complete_models_resources_work_restart
      holeKey fits admits graph templates checkEmpty stop order metadata seed formulas solver inventory
      caller memos before packet proper uv chosen bounded known ceiling bucketBound reserved ambient
      assignment whole satisfied old initialBound currentBound unary application filtered policies refuted
  obtain ⟨stableFuel, branches, stableFacts⟩ :=
    SourcePruningEnumerationSharedPrefixWork.checkpoint_resources_work_stable
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      caller memos before packet seed.2 (fun guard => guard ∈ seed.1) bounded known uv chosen
  dsimp only at branches stableFacts
  have baseline := policy stableFuel
  dsimp only at baseline
  refine ⟨policyFuel + stableFuel, ?_⟩
  rcases branches with ⟨cached, stable⟩ | ⟨checked, prefixHeap, stable⟩ |
    ⟨checked, prefixValue, prefixHeap, narrowedCache, _nonempty, stable⟩
  · have fixedAt (extra : Nat) :
        runPrefix holeKey fits admits graph templates stop order metadata
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            uv caller before memos.query =
          .parked cached.core (some cached)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata cached cached.core))) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm] using stable (policyFuel + extra)
    have baselineActual := fixedAt 0
    simp only [Nat.add_zero] at baselineActual
    rw [baselineActual] at baseline
    intro extra
    dsimp only
    have current := stableFacts (policyFuel + extra)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_left_comm] using current.1
    · simpa only [Nat.add_assoc, Nat.add_left_comm] using current.2.1
    · have debit := current.2.2 initialBound assignment
      rw [stable (policyFuel + extra)] at debit
      rw [fixedAt extra]
      exact debit
    · rw [fixedAt extra]
      exact baseline.2.2.2
  · have baselineActual :
        runPrefix holeKey fits admits graph templates stop order metadata
            (policyFuel + stableFuel) (policyFuel + stableFuel) (policyFuel + stableFuel)
            (policyFuel + stableFuel) (policyFuel + stableFuel) (policyFuel + stableFuel)
            uv caller before memos.query =
          .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) prefixHeap)
            (advanceCaller caller prefixHeap) memos.query (some []) none none none := by
      simpa only [SourcePruningEnumerationSelectedValueCaller.advance, Nat.add_comm] using stable policyFuel
    rw [baselineActual] at baseline
    exact False.elim baseline.2.2.2
  · have fixedPrefix (extra : Nat) : ∃ action : EnumerateM Symbol Constraint Unit,
        runPrefix holeKey fits admits graph templates stop order metadata
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            (policyFuel + stableFuel + extra) (policyFuel + stableFuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (prefixValue, some action) prefixHeap)
            (advanceCaller caller prefixHeap) memos.query
            (some [.ok ((), narrowedCache.core)]) (some narrowedCache)
            (some [.ok ((false, metadata), narrowedCache.core)]) none := by
      obtain ⟨action, actual⟩ := stable (policyFuel + extra)
      exact ⟨action, by simpa only [SourcePruningEnumerationSelectedValueCaller.advance,
        Nat.add_assoc, Nat.add_left_comm] using actual⟩
    obtain ⟨_firstAction, baselineActual⟩ := fixedPrefix 0
    simp only [Nat.add_zero] at baselineActual
    rw [baselineActual] at baseline
    obtain ⟨handle, scs, value, prefixMemos, admission, narrowedProper, narrowedModel,
      narrowedOrigins, preparationFuel, decoded, prepared, heap, entered, originalPreparationPost,
      preparation, enteredModel, enteredOrigins, accepted, ordinaryHeads, opaqueHead⟩ := baseline.2.2.2
    have preparationFacts := preparation.1
    rcases preparationFacts with ⟨preparationRunning, _lookup, _preparationPost, _enteredPacket,
      _stable, _ready, _stored, _counter, _values, flags, waiting, _available, _closed,
      _meaning, _satisfaction⟩
    have sameFrame := entered_frame narrowedCache entered flags waiting
    intro extra
    dsimp only
    have current := stableFacts (policyFuel + extra)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_left_comm] using current.1
    · simpa only [Nat.add_assoc, Nat.add_left_comm] using current.2.1
    · have debit := current.2.2 initialBound assignment
      obtain ⟨_debitAction, sourceActual⟩ := stable (policyFuel + extra)
      rw [sourceActual] at debit
      obtain ⟨_shiftedAction, shiftedActual⟩ := fixedPrefix extra
      rw [shiftedActual]
      exact debit
    · obtain ⟨_currentAction, actual⟩ := fixedPrefix extra
      rw [actual]
      refine ⟨handle, scs, value, prefixMemos, admission, narrowedProper, narrowedModel,
        narrowedOrigins, preparationFuel, decoded, prepared, heap, entered, originalPreparationPost,
        preparation, enteredModel, enteredOrigins, accepted, ordinaryHeads, ?_⟩
      intro boundary
      obtain ⟨headFuel, receipt, headCaller, saved, final, next, originalPost, prefixPost,
        resource, fragment, after, extended, models, callbackFuel, recorded, callbackCore,
        callbackPacket, pendingEq, workEq⟩ := opaqueHead boundary
      have headRunning := resource.1
      rw [admission.2.1] at headRunning
      have callbackResources := callbackPacket.1.1.1
      rcases callbackResources with ⟨_callbackPacket, _callbackStable, _callbackFrame,
        _types, _holes, _typing, _fits, _known, callbackRunning⟩
      have common := adequate_of_stable holeKey fits admits graph templates checkEmpty stop order metadata
        uv handle (policyFuel + stableFuel) preparationFuel headFuel callbackFuel
        caller (advanceCaller caller prefixHeap) before narrowedCache memos.query memos.query
        scs decoded prepared heap entered receipt fragment headCaller saved after recorded callbackCore
        checked prefixValue prefixHeap fixedPrefix preparationRunning sameFrame boundary headRunning models.1.1
        (fun callbackExtra => (callbackRunning callbackExtra).2.1)
        (fun callbackExtra recur => callbackPacket.2.2.2 callbackExtra recur stop order)
      exact ⟨headFuel, receipt, headCaller, saved, final, next, originalPost, prefixPost,
        resource, fragment, after, extended, models, callbackFuel, recorded, callbackCore,
        callbackPacket, pendingEq, workEq, common⟩

end MicroCFTA.SourcePruningEnumerationSharedCommonOpaqueRestart
