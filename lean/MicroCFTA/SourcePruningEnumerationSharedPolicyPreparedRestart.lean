import MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedWork
import MicroCFTA.SourcePruningEnumerationSharedRecordedModelWork
import MicroCFTA.SourcePruningEnumerationSharedPreparedHookCertificates

/-!
# One policy head and its actual recording restart

One policy producer retains the prefix, preparation and complete head packets.
One callback uses each head's same assignment and full memo bundle.
Original bounded pending IDs retain refutation under that assignment.
Original template policies give a false verdict and updated refutation.
The same callback preserves the head's pending size and scalar work.
This result ends at the actual restart and does not execute recursion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedRestart
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

open EnumerationDriver EnumerationCompressionFrame EnumerationProgress
open SourcePruningRecordTypes
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure continueWith)
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "CallbackResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem callback_from_original
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (proper : ProperState before.core)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol) (whole : Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap) meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment)
    (limit : Nat) (original : Nat → Term Symbol)
    (originalBounded : ∀ group ∈ metadata.pending, SourcePruningPartialMatch.PendingBound limit group)
    (agree : ∀ key < limit, assignment key = original key)
    (policies : SourcePruningTemplates.OriginPolicies templates whole)
    (refuted : ∀ group ∈ metadata.pending, Refutes original group)
    (inside : uv < before.core.counter)
    (filled : Fragments.fill assignment fragment = assignment uv) :
    ∃ (callbackFuel : Nat) (recorded : Bool × Metadata Typing) (callbackCore : Core),
      (((Packet formulas solver inventory caller memos recorded.2 (EnumerationExpandableIndex.frame callbackCore before) ∧
      RenderStable before.core callbackCore ∧ Frame before.core callbackCore ∧
      recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
      recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)) before.core recorded callbackCore ∧
        ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (recorded, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
            stop order,
          continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if recorded.1 then .complete [] caller memos.query
            else recur recorded.2 caller memos.query (EnumerationExpandableIndex.frame callbackCore before)
              (SourcePruningEnumerationRestart.decision stop order recorded.2
                (EnumerationExpandableIndex.frame callbackCore before))) ∧
      ProperState callbackCore ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) meaning assignment callbackCore ∧
      AssignmentOrigins whole callbackCore.counter assignment ∧
      (∀ (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat),
        SourcePruningEnumerationRestart.decision stop order recorded.2
          (EnumerationExpandableIndex.frame callbackCore before) ≠ some .stuck) ∧
      (templates = [] → recorded.1 = false) ∧
      (uv < before.core.counter → Fragments.fill assignment fragment = assignment uv →
        SourcePruningTemplates.OriginPolicies templates whole →
        (∀ group ∈ metadata.pending, Refutes assignment group) →
        recorded.1 = false ∧ ∀ group ∈ recorded.2.pending, Refutes assignment group)) ∧
      EnumerationStorageProgress.pendingSize callbackCore assignment =
        EnumerationStorageProgress.pendingSize before.core assignment ∧
      ∀ initialBound,
        SourcePruningEnumerationNativeWork.work initialBound (EnumerationExpandableIndex.frame callbackCore before) assignment =
          SourcePruningEnumerationNativeWork.work initialBound before assignment) ∧
      recorded.1 = false ∧
      (∀ group ∈ recorded.2.pending, Refutes assignment group) ∧
      ∀ extra (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → CallbackResult)
          stop order,
        continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment caller memos.query before =
          recur recorded.2 caller memos.query (EnumerationExpandableIndex.frame callbackCore before)
            (SourcePruningEnumerationRestart.decision stop order recorded.2
              (EnumerationExpandableIndex.frame callbackCore before)) := by
  have headRefuted := SourcePruningRecordTypes.pending_refutes_extension
    limit original assignment metadata originalBounded agree refuted
  obtain ⟨callbackFuel, recorded, callbackCore, retained, pendingEq, workEq⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources_models_work
      formulas solver inventory graph templates metadata uv fragment caller memos before seed
      packet allocated bounded known proper ambient meaning assignment whole satisfied origins
  have full := And.intro retained (And.intro pendingEq workEq)
  rcases retained with ⟨resource, _proper, _model, _origins, _notStuck, _empty, compatible⟩
  obtain ⟨accepted, nextRefuted⟩ := compatible inside filled policies headRefuted
  rcases resource with ⟨_packet, _stable, _frame, _types, _holes, _typing, _fits, _known, running⟩
  refine ⟨callbackFuel, recorded, callbackCore, full, accepted, nextRefuted, ?_⟩
  intro extra recur stop order
  have actual := (running extra).2.2 recur stop order
  simpa only [accepted, Bool.false_eq_true, ↓reduceIte] using actual

/-- One actual policy head retains its full packet and supplies its false callback restart. -/
theorem complete_models_resources_work_restart
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
                  SourcePruningEnumerationNativeWork.work initialBound before assignment)
      | _ => False := by
  obtain ⟨fuel, complete⟩ :=
    SourcePruningEnumerationSharedPolicyPreparedWork.complete_models_resources_work_proper_progress
      holeKey fits admits graph templates checkEmpty stop order metadata seed formulas solver inventory
      caller memos before packet proper uv chosen bounded known ceiling bucketBound reserved ambient
      assignment whole satisfied old initialBound currentBound unary application filtered
  refine ⟨fuel, ?_⟩
  intro extra
  have produced := complete extra
  dsimp only at produced ⊢
  rcases produced with ⟨valid, resources, prefixWork, heads⟩
  refine ⟨valid, resources, prefixWork, ?_⟩
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
    uv caller before memos.query = observed at heads ⊢
  cases observed with
  | stopped _ _ => exact heads
  | parked checked candidate raw =>
      cases candidate with
      | none => exact heads
      | some after => exact heads
  | narrowed checked narrowed reached saved action candidate right ordinary =>
      cases candidate with
      | none => exact heads
      | some narrowedCache =>
          obtain ⟨handle, scs, value, prefixMemos, admission, narrowedProper, narrowedModel,
            narrowedOrigins, bound, decoded, prepared, heap, entered, originalPreparationPost,
            preparation, enteredModel, enteredOrigins, accepted, ordinaryHeads, opaqueHead⟩ := heads
          have retained := preparation.1
          rcases retained with ⟨_running, _lookup, _preparationPost, enteredPacket, stable,
            enteredReady, _enteredStored, counter, _values, _flags, _waiting, _available,
            _closed, _meaning, _satisfaction⟩
          have admissionFacts := admission
          rcases admissionFacts with ⟨_prefixPost, _query, _narrowPacket, _narrowReady,
            _stored, _lookup, _available, _closed, incoming, _inputs, _ids, _length,
            narrowCounter, _waiting, _fits, _known⟩
          have originalCounter : entered.core.counter = before.core.counter := counter.trans narrowCounter
          have enteredIncoming : EnumerationReferences.IncomingAvoid uv entered.core :=
            EnumerationReferences.incoming_read uv narrowedCache.core entered.core stable incoming
          refine ⟨handle, scs, value, prefixMemos, admission, narrowedProper, narrowedModel,
            narrowedOrigins, bound, decoded, prepared, heap, entered, originalPreparationPost,
            preparation, enteredModel, enteredOrigins, accepted, ?_, ?_⟩
          · intro entry rows depth free ordinary
            obtain ⟨nonterminal, edge, rawMember, selected, resident, edgeAccepted,
              tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
              final, next, afterRoots, captured, coupled, afterProper, notStuck⟩ :=
              ordinaryHeads entry rows depth free ordinary
            rcases coupled with ⟨originalPost, prefixPost, resource, fragment, extended, completed,
              agree, inputModel, outputModel, filledOriginal, filled, afterOrigins, inherited,
              decreased, workDecreased⟩
            have models := And.intro completed (And.intro agree (And.intro inputModel
              (And.intro outputModel (And.intro filledOriginal (And.intro filled
                (And.intro afterOrigins (And.intro inherited (And.intro decreased workDecreased))))))))
            have fullResource := resource
            rcases resource with ⟨_running, headPost, querySame, growth, paths, storage, realized,
              counts, flags, _origin, _inputs, _protects, pendingTransfer, shape, headFits, headKnown⟩
            have completeShape : Safe after.core ∧ FragmentBound after.core.counter fragment ∧
                after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
                IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
                ∀ level frontier, EnumerationOrder.Stratified entered.core level frontier →
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
            have afterValid : SourcePruningEnumerationNativeBranchCompletion.CacheValid afterCaller after :=
              ⟨afterRoots, paths, storage, realized, counts, flags⟩
            have admitted : Admitted uv (.complete fragment afterCaller final.query after) :=
              ⟨afterValid, afterSafe, allocated, written, cleared, root⟩
            have history : FragmentHistory entered.core (.complete fragment afterCaller final.query after) :=
              ⟨growth, pendingFragment, orderedGain⟩
            have pending := pendingTransfer enteredPacket.pending enteredIncoming
            obtain ⟨level, frontier, ordered⟩ := enteredPacket.ordered
            have headPacket := SourcePruningEnumerationSharedPreparedRecursive.receipt_packet
              formulas solver next afterCaller final metadata entered.core uv fragment after level frontier
              headPost.context admitted history pending ordered enteredPacket.bounded
            have headAgreement : ∀ key < before.core.counter, extended key = assignment key := by
              intro key inside
              apply agree key
              simpa only [originalCounter] using inside
            have inside : uv < after.core.counter := Nat.lt_of_lt_of_le enteredReady.inside growth
            obtain ⟨callbackFuel, recorded, callbackCore, callbackFull, verdict, refutedAfter, restart⟩ :=
              callback_from_original formulas solver next graph templates metadata uv fragment
                afterCaller final after
                (advance (preparedSeed seed)
                  (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries))
                headPacket allocated headFits headKnown afterProper ambient
                (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                extended whole outputModel afterOrigins before.core.counter assignment packet.bounded
                headAgreement policies refuted inside filled
            have pendingEq := callbackFull.2.1
            have workEq := callbackFull.2.2 initialBound
            have restartAtReceipt := restart
            simp only [querySame] at restartAtReceipt
            refine ⟨nonterminal, edge, rawMember, selected, resident, edgeAccepted,
              tries, residual, projected, r, n, p, h, k, afterCaller, after, savedQueries,
              final, next, afterRoots, captured,
              ⟨originalPost, prefixPost, fullResource, fragment, extended, models,
                callbackFuel, recorded, callbackCore,
                ⟨callbackFull, verdict, refutedAfter, restartAtReceipt⟩, ?_, ?_⟩, afterProper, notStuck⟩
            · rw [pendingEq]
              exact decreased
            · rw [workEq]
              exact workDecreased
          · intro boundary
            obtain ⟨headBound, receipt, headCaller, headQueries, final, next,
              originalPost, prefixPost, resource, fragment, after, extended, models,
              pendingEq, workDecreased, afterProper, notStuck⟩ := opaqueHead boundary
            have oldOpaque := And.intro models (And.intro pendingEq
              (And.intro workDecreased (And.intro afterProper notStuck)))
            rcases models with ⟨completed, _installed, agree, _inputModel, outputModel,
              _filledOriginal, filled, afterOrigins, _inherited, _pendingSame, _workSame, _progress⟩
            have fullResource := resource
            rcases resource with ⟨_running, headPost, querySame, _advance, admitted, pending,
              history, headFits, headKnown, _shape, _finalization⟩
            rw [completed] at admitted pending history
            obtain ⟨level, frontier, ordered⟩ := enteredPacket.ordered
            have headPacket := SourcePruningEnumerationSharedPreparedRecursive.receipt_packet
              formulas solver next headCaller final metadata entered.core uv fragment after level frontier
              headPost.context admitted history pending ordered enteredPacket.bounded
            have allocated : FragmentBound after.core.counter fragment := admitted.2.2.1
            have headAgreement : ∀ key < before.core.counter, extended key = assignment key := by
              intro key inside
              apply agree key
              simpa only [originalCounter] using inside
            have inside : uv < after.core.counter := Nat.lt_of_lt_of_le enteredReady.inside history.1
            obtain ⟨callbackFuel, recorded, callbackCore, callbackFull, verdict, refutedAfter, restart⟩ :=
              callback_from_original formulas solver next graph templates metadata uv fragment
                headCaller final after (advance (preparedSeed seed) (scs.length + 1))
                headPacket allocated headFits headKnown afterProper ambient
                (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
                extended whole outputModel afterOrigins before.core.counter assignment packet.bounded
                headAgreement policies refuted inside filled
            have callbackPending := callbackFull.2.1
            have callbackWork := callbackFull.2.2 initialBound
            have restartAtReceipt := restart
            simp only [querySame] at restartAtReceipt
            refine ⟨headBound, receipt, headCaller, headQueries, final, next,
              originalPost, prefixPost, fullResource, fragment, after, extended, oldOpaque,
              callbackFuel, recorded, callbackCore,
              ⟨callbackFull, verdict, refutedAfter, restartAtReceipt⟩, ?_, ?_⟩
            · exact callbackPending.trans pendingEq
            · rw [callbackWork]
              exact workDecreased

end MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedRestart
