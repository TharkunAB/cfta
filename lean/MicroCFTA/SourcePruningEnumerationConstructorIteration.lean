import MicroCFTA.SourcePruningEnumerationAcceptedConstructorProgress
import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeEndpointProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationNativeProgress

namespace MicroCFTA.SourcePruningEnumerationConstructorIteration
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationProgress
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actually selected accepted constructor retains its full model result and derives the next recursive packet. -/
theorem accepted_constructor_packet
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (memos : Memos)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (proper : ProperState before.core) (target handle : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand target))
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentLookup : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term : Term Symbol)
    (parentValue : assignment target = term)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (fragment : Fragment) (afterCaller : Caller (bits + 2))
      (recorded finalized : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (extended : Nat → Term Symbol),
      (
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          scs edge caller before memos.query = .complete fragment afterCaller savedQueries recorded) ∧
      (∀ ek, SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap (k + ek)
        target fragment recorded = some finalized) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended before.core ∧
      Fragments.fill extended fragment = term ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended recorded.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended finalized.core ∧
      Safe finalized.core ∧ EnumerationValidity.Canonical finalized.core ∧
      Roots finalized.core.representatives afterRoots ∧ StorageValid finalized.core ∧
      PendingRealized afterCaller.checked.native.machine.heap finalized.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots finalized.core.values finalized.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((finalized.core.values[slot]?).getD .eliminated) = some (finalized.expandable slot)) ∧
      Fits (advance seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).2
        afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ∧
      EnumerationStorageProgress.pendingSize finalized.core extended + 1 ≤
        EnumerationStorageProgress.pendingSize before.core assignment
      ) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          target scs edge caller before memos.query =
          some (.complete fragment afterCaller savedQueries finalized)) ∧
      SourcePruningEnumerationRecursive.Packet formulas solver next afterCaller final metadata finalized ∧
      ProperState finalized.core ∧
      SourcePruningEnumerationNativeBranchCompletion.Admitted target
        (.complete fragment afterCaller savedQueries finalized) ∧
      SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core
        (.complete fragment afterCaller savedQueries finalized) ∧
      ∀ (uv : Nat) (node : Option Nat) (bucket : List Suspended),
        finalized.core.values[uv]? = some (UVarValue.unenumerated node bucket) →
        InputsPending finalized.core bucket ∧ ∀ sc ∈ bucket, sc.var < finalized.core.counter := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨ready, incoming, _native⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before target packet.valid packet.safe chosen
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    packet.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core packet.pending target (some handle) scs stored
  have canonical := proper_canonical before.core proper
  have sourceValid : EnumerationSemantics.ValidSuspended scs :=
    canonical _ (List.mem_of_getElem? stored)
  obtain ⟨actualParent, parentFound, parentKnown, parentIsClosed⟩ := realized target handle scs stored
  have parentSame : actualParent = .node parentEntry edges depth free :=
    Option.some.inj (parentFound.symm.trans parentLookup)
  have parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free) := by
    simpa only [parentSame] using parentKnown
  have parentClosed : free = [] := by
    simpa only [parentSame, Value.free] using parentIsClosed
  have inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc := by
    have slotModel := satisfied.1.2 target
    simp only [heap, stored, Option.getD_some, slot, Option.map_some, Fragments.slotSatisfies] at slotModel
    intro sc member
    have obligation := slotModel.2 (fun assn value => Suspended.Holds assn value sc)
      (List.mem_map.mpr ⟨sc, member, rfl⟩)
    simpa only [parentValue] using obligation
  obtain ⟨_actualTries, _actualResidual, _terms, _projection, _validTries, _shape,
    _childMeanings, _length, allowed, _own, _residualHeld⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry edges depth free edge scs packet.context parentAvailable selected ambient assignment term
      accepted inherited
  obtain ⟨r, n, p, h, k, fragment, afterCaller, recorded, finalized, savedQueries, final, next,
    afterRoots, extended, original⟩ :=
    SourcePruningEnumerationAcceptedConstructorProgress.accepted_constructor_decreases
      seed formulas solver inventory caller before checkEmpty parentEntry edges depth free edge scs roots memos
      packet.context selected packet.safe realized paths counts flags bounded pending canonical target handle
      stored parentLookup ready.root ambient assignment term parentValue satisfied accepted tries residual projected
      fits reserved known
  have retainedOriginal := original
  rcases original with ⟨selectedRun, finalizedRun, post, querySame, _agree, _originalModel,
    _filled, _recordedModel, _finalModel, finalSafe, _finalCanonical, finalPaths, finalStorage,
    finalRealized, finalCounts, finalFlags, _finalFits, _finalKnown, _decrease⟩
  have capturedRun : ∀ er en P H ek, p ≤ P → h ≤ H →
      SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
        target scs edge caller before memos.query =
        some (.complete fragment afterCaller savedQueries finalized) := by
    intro er en P H ek enoughP enoughH
    simp only [SourcePruningEnumerationCapturedEdge.run, selectedRun er en P H ek enoughP enoughH,
      finalizedRun ek, Option.map_some]
  obtain ⟨otherR, otherN, otherP, otherH, otherK, otherCaller, otherAfter, otherQueries,
    _otherMemos, _otherInventory, _otherRoots, otherResult, otherRun, _otherPost,
    _otherQuerySame, growth, _otherPaths, _otherStorage, _otherRealized, _otherCounts,
    _otherFlags, _origin, _retained, _protected, pendingHistory, shape, _otherFits, _otherKnown⟩ :=
    SourcePruningEnumerationCapturedEdge.complete_with_history_resources
      seed formulas solver inventory caller before checkEmpty target handle scs parentEntry edges depth free
      edge roots memos packet.context ready stored parentLookup realized selected paths counts flags pending
      allowed tries residual projected fits reserved known
  have resultSame : SourcePruningEnumerationSelectedEdge.Result.complete fragment afterCaller savedQueries finalized =
      otherResult := by
    apply Option.some.inj
    exact (capturedRun otherR otherN (p + otherP) (h + otherH) otherK (by omega) (by omega)).symm.trans
      (by simpa only [Nat.add_comm] using otherRun r n (p + otherP) (h + otherH) k (by omega) (by omega))
  rcases shape with ⟨otherFragment, completed, _otherSafe, fragmentBound, finalStored,
    cleared, targetRoot, fragmentPending, advancedOrder⟩ | ⟨fragments, outer, waiting, stopped⟩
  · rcases SourcePruningEnumerationSelectedEdge.Result.complete.inj (resultSame.trans completed) with
      ⟨fragmentSame, callerSame, queriesSame, cacheSame⟩
    subst otherFragment
    subst otherCaller
    subst otherQueries
    subst otherAfter
    have finalPending := pendingHistory packet.pending incoming
    have admitted : SourcePruningEnumerationNativeBranchCompletion.Admitted target
        (.complete fragment afterCaller savedQueries finalized) :=
      ⟨⟨afterRoots, finalPaths, finalStorage, finalRealized, finalCounts, finalFlags⟩,
        finalSafe, fragmentBound, finalStored, cleared, targetRoot⟩
    have history : SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core
        (.complete fragment afterCaller savedQueries finalized) :=
      ⟨growth, fragmentPending, advancedOrder⟩
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    have returnedPacket : SourcePruningEnumerationRecursive.Packet
        formulas solver next afterCaller final metadata finalized :=
      SourcePruningEnumerationRecursive.receipt_packet before.core target fragment finalized level frontier
        post.context admitted history finalPending ordered packet.bounded
    have recordedProper : ProperState recorded.core := by
      have observed := SourcePruningEnumerationSelectedEdge.observed_cache_proper caller before checkEmpty
        parentEntry edges depth free edge scs roots memos packet.context parentAvailable parentClosed selected
        packet.safe realized paths counts flags bounded pending allowed tries residual projected proper sourceValid
        (selectedRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _))
      exact observed
    have finalProper := SourcePruningEnumerationFinalize.run_proper afterCaller.checked.native.machine.heap
      (k + 0) target fragment recorded finalized recordedProper (finalizedRun 0)
    refine ⟨r, n, p, h, k, fragment, afterCaller, recorded, finalized, savedQueries, final, next,
      afterRoots, extended, retainedOriginal, capturedRun, returnedPacket, finalProper, admitted, history, ?_⟩
    intro uv node bucket found
    exact ⟨EnumerationReferences.pending_inputs finalized.core returnedPacket.pending uv node bucket found,
      returnedPacket.safe.1.values _ (List.mem_of_getElem? found)⟩
  · rw [← resultSame] at stopped
    cases stopped

end MicroCFTA.SourcePruningEnumerationConstructorIteration
