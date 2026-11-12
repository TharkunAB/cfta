import MicroCFTA.SourcePruningEnumerationSharedPreparedHeadWork
import MicroCFTA.SourcePruningEnumerationSharedPrefixTargetWork
import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.SourcePruningEnumerationPrefixCoverage
import MicroCFTA.SourcePruningEnumerationPrefixProperHistory

/-!
# One policy prefix before the same prepared branch model

The current decision supplies the actual selected slot.
The literal common prefix retains its model under the three policy tests.
One admission supplies its caller, cache and complete memo bundle.
One preparation then supplies the same captured branch and local progress.
The parked case retains its own cache and model.
The same prefix and head charge the selected activity exactly once.
Ordinary and opaque heads retain progress from the original cache.
The accepting branch uses all stored rows. It makes no claim about other selectors.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedWork
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

/-- The actual policy prefix supplies one prepared model packet and its local progress. -/
theorem complete_models_resources_work_proper_progress
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
      admits (holeKey metadata.typing uv) annotation = true) :
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
      | .narrowed _ _ reached saved _ (some narrowedCache) _ _ =>
          ∃ (handle : Nat) (scs : List Suspended) (value : Node) (prefixMemos : Memos),
            (Post formulas solver inventory caller reached prefixMemos ∧ prefixMemos.query = saved ∧
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
                result = .complete fragment afterCaller savedQueries after ∧
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
                (receipt = .complete fragment headCaller saved after ∧
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
                  SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck)
      | _ => False := by
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, complete⟩ := SourcePruningEnumerationSelectedStep.prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before (order metadata) uv roots packet.context packet.safe packet.pending
    selection realized paths counts flags
  have ready := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  refine ⟨fuel, ?_⟩
  intro extra
  dsimp only
  have valid := complete extra
  have work := SourcePruningEnumerationSharedPrefixWork.retained_work_target_debit
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (fuel + extra) uv initialBound assignment caller memos before packet chosen _ valid rfl
  have resources := SourcePruningEnumerationSelectedStep.prefix_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (fuel + extra) uv caller before memos seed.2 (fun guard => guard ∈ seed.1)
    packet.context realized bounded known _ valid
  have model := SourcePruningEnumerationSelectedStep.prefix_accepting
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (fuel + extra) uv caller before memos packet.context ready realized valid ambient
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment satisfied unary application filtered
  have properAt := SourcePruningEnumerationSelectedStep.prefix_proper
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (fuel + extra) uv caller before memos proper valid
  have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (fuel + extra) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
    bounded known _ valid
  refine ⟨valid, resources, ?_, ?_⟩
  · generalize equation : runPrefix holeKey fits admits graph templates stop order metadata
      (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
      uv caller before memos.query = observed at work ⊢
    cases observed with
    | stopped _ _ => trivial
    | parked checked candidate raw =>
        cases candidate with
        | none => trivial
        | some after => exact work
    | narrowed checked prepared reached saved action candidate right ordinary =>
        cases candidate with
        | none => trivial
        | some after => exact work
  · generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
      (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
      uv caller before memos.query = observed at valid resources model properAt admission work ⊢
    have currentValid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos observed := valid
    cases observed with
    | stopped _ _ => exact model.elim
    | parked checked candidate raw =>
        cases candidate with
        | none => exact model.elim
        | some after =>
            have returned := SourcePruningEnumerationRecursive.prefix_packet
              holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
              (fuel + extra) uv caller memos before packet (.parked checked (some after) raw) currentValid
            have origins : AssignmentOrigins whole after.core.counter assignment := by
              rw [currentValid.2.2.1]
              exact old
            exact ⟨returned, properAt, model, origins⟩
    | narrowed checked narrowed reached saved action candidate right ordinary =>
        cases candidate with
        | none => exact model.elim
        | some narrowedCache =>
            obtain ⟨handle, scs, value, prefixMemos, admitted⟩ := admission
            have admissionPacket := admitted
            rcases admitted with ⟨prefixPost, _querySame, afterPacket, afterReady, stored,
              _decoded, _available, _closed, incoming, _pending, _ids, lengthBound,
              counter, _waiting, afterFits, afterKnown⟩
            have origins : AssignmentOrigins whole narrowedCache.core.counter assignment := by
              rw [counter]
              exact old
            have currentFits : Fits (narrowSeed seed).2 reached.checked := afterFits
            refine ⟨handle, scs, value, prefixMemos, admissionPacket, properAt, model, origins, ?_⟩
            have prefixPending := work.2.2.1
            have currentPending : EnumerationStorageProgress.pendingSize narrowedCache.core assignment ≤ initialBound := by
              rw [prefixPending]
              exact currentBound
            have prefixDebit := work.2.2.2.2
            have prefixWork : SourcePruningEnumerationNativeWork.work initialBound narrowedCache assignment ≤
                SourcePruningEnumerationNativeWork.work initialBound before assignment := by omega
            obtain ⟨bound, decoded, prepared, heap, entered, preparation, enteredModel,
              enteredOrigins, accepted, ordinaryHeads, opaqueHead⟩ :=
              SourcePruningEnumerationSharedPreparedHeadWork.complete_models_resources_work_proper_progress
                seed formulas solver inventory reached prefixMemos metadata narrowedCache uv handle scs checkEmpty
                afterPacket afterReady stored incoming currentFits afterKnown ceiling
                (Nat.le_trans lengthBound bucketBound) reserved ambient assignment whole model origins properAt
                initialBound currentPending
            have preparationFacts := preparation.1
            rcases preparationFacts with ⟨_running, _lookup, preparationPost, _rest⟩
            refine ⟨bound, decoded, prepared, heap, entered,
              prefixPost.trans preparationPost, preparation, enteredModel, enteredOrigins, accepted, ?_, ?_⟩
            · intro entry rows depth free ordinary
              obtain ⟨nonterminal, edge, rawMember, selected, resident, edgeAccepted,
                tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
                final, next, afterRoots, captured, coupled, afterProper, notStuck⟩ :=
                ordinaryHeads entry rows depth free ordinary
              rcases coupled with ⟨headPost, resource, fragment, extended, completed, agree,
                inputModel, outputModel, filledOriginal, filled, afterOrigins, inherited, decreased, workDecreased⟩
              rw [prefixPending] at decreased
              have originalWork := Nat.lt_of_lt_of_le workDecreased prefixWork
              have models := And.intro completed
                (And.intro agree (And.intro inputModel (And.intro outputModel
                  (And.intro filledOriginal (And.intro filled (And.intro afterOrigins
                    (And.intro inherited (And.intro decreased originalWork))))))))
              exact ⟨nonterminal, edge, rawMember, selected, resident, edgeAccepted,
                tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
                final, next, afterRoots, captured,
                ⟨prefixPost.trans headPost, headPost, resource, ⟨fragment, extended, models⟩⟩,
                afterProper, notStuck⟩
            · intro boundary
              obtain ⟨headBound, receipt, headCaller, headQueries, final, next, headPost, resource,
                fragment, after, extended, models, pendingEq, headWork, afterProper, notStuck⟩ := opaqueHead boundary
              have originalWork : SourcePruningEnumerationNativeWork.work initialBound after extended + 1 =
                  SourcePruningEnumerationNativeWork.work initialBound before assignment := by
                cases active : narrowedCache.expandable uv <;>
                  simp only [active, Bool.false_eq_true, ↓reduceIte] at prefixDebit headWork <;> omega
              exact ⟨headBound, receipt, headCaller, headQueries, final, next,
                prefixPost.trans headPost, headPost, resource, fragment, after, extended, models,
                pendingEq.trans prefixPending, originalWork, afterProper, notStuck⟩

end MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedWork
