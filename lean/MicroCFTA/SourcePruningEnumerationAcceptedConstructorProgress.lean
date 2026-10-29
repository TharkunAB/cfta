import MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
import MicroCFTA.SourcePruningEnumerationTraversalModelStorageProgress
import MicroCFTA.SourcePruningEnumerationParentChildSeparation
import MicroCFTA.SourcePruningEnumerationSelectedEdgeCanonical
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeFinishLanguage

namespace MicroCFTA.SourcePruningEnumerationAcceptedConstructorProgress
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
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

private theorem suspended_old_slot (count : Nat) (state : EnumerationState.State Symbol Constraint)
    (uv : Nat) (inside : uv < state.values.length) :
    (suspendedState count state).values[uv]? = state.values[uv]? := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change (suspendedState count (allocated none state)).values[uv]? = state.values[uv]?
    rw [ih (allocated none state) (by simp only [allocated, List.length_append, List.length_singleton]; omega)]
    simp only [allocated, List.getElem?_append_left inside]

private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
    exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A prepared constructor preserves the captured target and the complete progress result. -/
theorem accepted_prepared_constructor_decreases
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (canonical : EnumerationValidity.Canonical before.core)
    (target handle : Nat) (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
    (root : IsRoot before.core.representatives target)
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
        EnumerationStorageProgress.pendingSize before.core assignment := by
  have insideValues : target < before.core.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have inside : target < before.core.counter := by
    have aligned : before.core.counter = before.core.values.length := safe.1.aligned
    omega
  have inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc := by
    have slotModel := satisfied.1.2 target
    simp only [heap, stored, Option.getD_some, slot, Option.map_some, Fragments.slotSatisfies] at slotModel
    intro sc member
    have obligation := slotModel.2 (fun assn value => Suspended.Holds assn value sc)
      (List.mem_map.mpr ⟨sc, member, rfl⟩)
    simpa only [parentValue] using obligation
  obtain ⟨actualTries, actualResidual, terms,
    ⟨projection, validTries, parentShape, childMeanings, _length, allowed, _ownEqualities, residualHeld⟩,
    action, own, ownPacket, ownAssignment, ownAgree, _originalOwnModel, ownModel, _combined, childModels, ownCost⟩ :=
    SourcePruningEnumerationOwnChildModelProgress.accepted_own_children formulas solver inventory caller before
      parentEntry edges depth free edge scs roots memos initial parentAvailable parentClosed selected safe realized
      paths counts flags bounded pending ambient assignment term satisfied accepted inherited
  have projectionSame : (actualTries, actualResidual) = (tries, residual) :=
    Option.some.inj (projection.symm.trans projected)
  obtain ⟨triesSame, residualSame⟩ := Prod.mk.inj projectionSame
  subst actualTries
  subst actualResidual
  rcases ownPacket with ⟨_prepared, ownRun, _raw, ownCore, ownCounter, ownForest, ownSafe,
    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, _ownProtects⟩
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have sourceValid : EnumerationSemantics.ValidSuspended scs :=
    canonical _ (List.mem_of_getElem? stored)
  have childSeparation : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Avoids own.core.representatives target bucket :=
    SourcePruningEnumerationParentChildSeparation.edge_children_avoid_parent
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      own.core ownAssignment target edge terms scs before.core.counter tries ownModel
      (by rw [ownAgree target inside, parentValue, parentShape]) sourceValid validTries
      (SourceEqualityPCSGuard.holds formulas solver) ambient childModels
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next,
    afterRoots, result, receipt, acceptingChildren⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting_pendingSize
      seed formulas solver inventory caller own checkEmpty inputs roots memos initial ownSafe ownPaths
      ownCounts ownFlags ownRealized genuine fits reserved known
  rcases receipt with ⟨childrenRun, post, querySame, growth, afterPaths, storage, afterRealized,
    afterCounts, afterFlags, _origin, _protectedEnumerated, protectedRoots, _references,
    _pendingReferences, fragmentBounds, childShape, returnedFits, returnedKnown, _oldAccepting⟩
  obtain ⟨extended, tailAgree, _ownExtended, completed, childrenFilled, afterModel, childCost⟩ :=
    acceptingChildren ambient
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      ownAssignment terms ownModel childModels
  have ownGrowth : before.core.counter ≤ own.core.counter := by
    rw [ownCounter]
    omega
  have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
    intro uv bound
    exact (tailAgree uv (Nat.lt_of_lt_of_le bound ownGrowth)).trans (ownAgree uv bound)
  have ownRoot : IsRoot own.core.representatives target := by simpa only [ownForest] using root
  have ownInside : target < own.core.counter := Nat.lt_of_lt_of_le inside ownGrowth
  have parentProtected := protectedRoots target ownInside ownRoot childSeparation
  have ownStored : own.core.values[target]? = some (.unenumerated (some handle) scs) := by
    rw [ownCore, suspended_old_slot tries.length before.core target insideValues]
    exact stored
  have afterStored := parentProtected.value.trans ownStored
  have filled : Fragments.fill extended (.node edge.entry.key.symbol fragments) = term := by
    simp only [Fragments.fill, childrenFilled, parentShape]
  have afterSafe : Safe after.core := by
    rcases childShape with success | ⟨outer, waiting, stopped⟩
    · exact success.2.1
    · rw [completed] at stopped
      cases stopped
  have parentFragmentBound := node_bound after.core.counter edge.entry.key.symbol fragments fragmentBounds
  let recorded := SourcePruningEnumerationSelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after
  have recordedSafe := SourcePruningEnumerationSelectedEdge.finish_safe residual
    (.node edge.entry.key.symbol fragments) after afterSafe parentFragmentBound
  have recordedModel := (SourcePruningEnumerationSelectedEdge.finish_semantics residual
    (.node edge.entry.key.symbol fragments) after
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap)
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true) extended).mpr
      ⟨afterModel, by simpa only [filled] using residualHeld⟩
  have selectedRun : ∀ er en P H ek, p ≤ P → h ≤ H →
      SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
        scs edge caller before memos.query =
        .complete (.node edge.entry.key.symbol fragments) afterCaller savedQueries recorded := by
    intro er en P H ek enoughP enoughH
    have running := (childrenRun er en P H ek enoughP enoughH).trans completed
    have readback : (List.map (fun input => (input.1, input.2.1))
        (inputs.map (fun input =>
          (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1)))) = inputs := by
      simp only [List.map_map]
      exact List.map_id _
    dsimp only [inputs] at readback running
    simp only [SourcePruningEnumerationSelectedEdge.run, ownRun, readback, running]
    rfl

  have recordedCanonical := SourcePruningEnumerationSelectedEdge.complete_canonical
    caller before checkEmpty parentEntry edges depth free edge scs roots memos initial parentAvailable
    parentClosed selected safe realized paths counts flags bounded pending allowed tries residual projected
    canonical sourceValid (selectedRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _))
  have recordedStored : recorded.core.values[target]? = some (.unenumerated (some handle) scs) := afterStored
  obtain ⟨finalFuel, finalized, finalRun, _finalRaw, written, _finalStored, _finalFlag, _finalWaiting,
    finalPaths, finalCounts, finalFlags, finalStorage, finalRealized, finalSafe⟩ :=
    SourcePruningEnumerationFinalize.complete afterCaller.checked.native.machine.heap recorded target
      (.node edge.entry.key.symbol fragments) (.unenumerated (some handle) scs) recordedStored
      afterRoots afterPaths afterCounts afterFlags recordedSafe.1 parentFragmentBound afterRealized
  have finalizePoint := finalRun 0
  simp only [Nat.add_zero] at finalizePoint
  have finalizedCanonical := SourcePruningEnumerationFinalize.run_canonical
    afterCaller.checked.native.machine.heap finalFuel target (.node edge.entry.key.symbol fragments)
    recorded finalized recordedCanonical finalizePoint
  have parentEquation : Fragments.fill extended (.node edge.entry.key.symbol fragments) = extended target :=
    filled.trans ((agree target inside).trans parentValue).symm
  have finalizedModel := (SourcePruningEnumerationFinalize.written_semantics recorded.core finalized.core target
    (.node edge.entry.key.symbol fragments) ((List.getElem?_eq_some_iff.mp recordedStored).1) written
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap)
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true) extended).mpr
      ⟨EnumerationFrame.neutralize_satisfies _ _ extended target recorded.core recordedModel, parentEquation⟩
  have decrease := SourcePruningEnumerationStorageProgress.finalize_pendingSize
    afterCaller.checked.native.machine.heap finalFuel target handle (.node edge.entry.key.symbol fragments)
    scs recorded finalized extended recordedStored finalizePoint
  have recordedCost : EnumerationStorageProgress.pendingSize recorded.core extended =
      EnumerationStorageProgress.pendingSize after.core extended := rfl
  rw [recordedCost, (agree target inside).trans parentValue, parentShape, NumberedTerms.size] at decrease
  have originalModel := (state_assignment_congr _ _ before.core safe.1 extended assignment agree).mpr satisfied
  refine ⟨r, n, p, h, k + finalFuel, .node edge.entry.key.symbol fragments, afterCaller,
    recorded, finalized, savedQueries, final, next, afterRoots, extended, ?_, ?_, post, querySame,
    agree, originalModel, filled, recordedModel, finalizedModel,
    finalSafe recordedSafe parentProtected.root, finalizedCanonical, finalPaths, finalStorage,
    finalRealized, finalCounts, finalFlags, returnedFits, returnedKnown, ?_⟩
  · intro er en P H ek enoughP enoughH
    simpa only [Nat.add_assoc] using selectedRun er en P H (finalFuel + ek) enoughP enoughH
  · intro ek
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRun (k + ek)
  · rw [ownCost] at childCost
    omega

/-- Original accepted constructor inputs derive an actual mixed step with a strict pending-cost decrease. -/
theorem accepted_constructor_decreases
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (canonical : EnumerationValidity.Canonical before.core)
    (target handle : Nat) (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentLookup : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (root : IsRoot before.core.representatives target)
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
        EnumerationStorageProgress.pendingSize before.core assignment := by
  obtain ⟨actualParent, parentFound, parentKnown, parentIsClosed⟩ := realized target handle scs stored
  have parentSame : actualParent = .node parentEntry edges depth free :=
    Option.some.inj (parentFound.symm.trans parentLookup)
  have parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free) := by
    simpa only [parentSame] using parentKnown
  have parentClosed : free = [] := by
    simpa only [parentSame, Value.free] using parentIsClosed
  exact accepted_prepared_constructor_decreases seed formulas solver inventory caller before checkEmpty
    parentEntry edges depth free edge scs roots memos initial selected safe realized paths counts flags
    bounded pending canonical target handle stored parentAvailable parentClosed root ambient assignment term
    parentValue satisfied accepted tries residual projected fits reserved known

end MicroCFTA.SourcePruningEnumerationAcceptedConstructorProgress
