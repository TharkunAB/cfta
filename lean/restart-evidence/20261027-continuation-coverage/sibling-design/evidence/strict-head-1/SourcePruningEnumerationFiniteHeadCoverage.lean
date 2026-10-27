import MicroCFTA.SourcePruningEnumerationFiniteHeadResources
import MicroCFTA.SourcePruningEnumerationNativeHeadCoverage

/-!
# Constructive coverage for an actual finite recursive head

The original finite head packet remains available.
An accepted edge constructs the actual captured receipt.
The callback retains its exact outcome and full memo state.
The operational bound precedes the semantic observer.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)
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
local notation "finiteStep" => SourcePruningEnumerationFiniteReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep the full finite head packet and construct each accepted captured receipt. -/
theorem head_finite_complete_resources_accepting
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
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
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
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
            extended afterCache.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet bounded known
    parentEntry storedEdges depth free available edge selected
  have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  obtain ⟨r, n, p, h, k, receipt, middleCaller, saved, middleMemos, middleInventory,
    headRun, headPost, headQueries, admitted, headPending, history, shape, headFits, headKnown, accepting⟩ :=
    SourcePruningEnumerationNativeBranchCompletion.head_complete_resources_accepting seed formulas solver inventory caller before
      checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos packet.context ready stored decoded
      realized selected paths counts flags pending bounded (reserved.edge costBound) known
  have headRun0 := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at headRun0
  have cacheBounds := SourcePruningEnumerationNativeBranchCompletion.observed_head_cache_bounds
    checkEmpty r n p h k uv scs edge caller before memos.query
    (scalar seed.2) (guardWidth seed.1) children own receipt headRun0
  have padding := SourcePruningEnumerationRecursiveReservation.head_padding seed inherited
    (edgeCost scs before.core.counter edge) costBound
  have boundedHead := headFits.mono padding.1
  have knownHead : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
      middleCaller.checked.native.machine.heap :=
    fun key resident found => padding.2 (headKnown key resident found)
  have receiptPending := headPending packet.pending incoming
  let headBound := r + n + p + h + k
  have headAt (w : Nat) (large : headBound ≤ w) :
      SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w uv scs edge caller before memos.query = some receipt := by
    have rl : r ≤ w := by dsimp [headBound] at large; omega
    have nl : n ≤ w := by dsimp [headBound] at large; omega
    have pl : p ≤ w := by dsimp [headBound] at large; omega
    have hl : h ≤ w := by dsimp [headBound] at large; omega
    have kl : k ≤ w := by dsimp [headBound] at large; omega
    have observed := headRun (w - r) (w - n) w w (w - k) pl hl
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using observed
  rcases shape with advanced | unsupported
  · have advancedQuery : advance receipt = some (middleCaller, middleMemos.query) := by
      simpa only [headQueries] using advanced
    have mass := SourcePruningEnumerationRecursiveReservation.head_mass_le seed capturedMass inherited
      before scs receipt initialMass inheritedLength cacheBounds
    obtain ⟨callbackFuel, outcome, callbackRun, resources⟩ := receipt_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver recursiveFuel recursive
      inventory middleInventory
      caller middleCaller memos middleMemos before uv receipt packet headPost advancedQuery admitted receiptPending history
      (afterHead seed inherited) (massCeil seed capturedMass inherited) boundedHead knownHead
      selectionMembers selectionLength (by cases receipt <;> exact mass) reserved.2
    have fullResources : OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome :=
      resources.post headPost
    refine ⟨headBound + callbackFuel, receipt, middleCaller, saved, middleMemos, middleInventory,
      ?_, headPost, headQueries, admitted, receiptPending, history, cacheBounds, boundedHead, knownHead,
      .inr ⟨outcome, advancedQuery, ?_, fullResources, ?_⟩, accepting⟩
    · intro extra
      exact headAt (headBound + callbackFuel + extra) (by omega)
    · intro extra
      have actual := callbackRun (headBound + extra)
      have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
      rw [common] at actual
      exact actual
    · cases outcome with
      | stopped _ _ _ => trivial
      | complete outputs actual queries =>
          obtain ⟨next, final, post, query, captured, returnedFits, returnedKnown, _outputs⟩ :=
            SourcePruningEnumerationRecursive.completed_captured_packet formulas solver inventory caller memos
              metadata before (finiteStep recursiveFuel seed capturedMass inherited) outputs actual queries packet fullResources
          exact ⟨next, final, post, query, captured, returnedFits, returnedKnown⟩
  · exact ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      fun extra => headAt (headBound + extra) (by omega), headPost, headQueries,
      admitted, receiptPending, history, cacheBounds, boundedHead, knownHead, .inl unsupported, accepting⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
