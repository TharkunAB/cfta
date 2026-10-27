import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourceFlatPruningSelectedEdge
import MicroCFTA.SourceFlatPruningOwnObservation
import MicroCFTA.SourceFlatPruningTraversalCompletion

/-!
# Original selected-edge completion with direct-parent execution

The original own-prefix packet supplies the actual flat staged payload.
The same traversal witnesses supply the reached caller and complete memos.
The residual is recorded only after every child succeeds.
-/
namespace MicroCFTA.SourceFlatPruningSelectedCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSelectedEdge (Result Ranges run finish finish_safe finish_protected)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original selected-edge admission retains the full earlier packet and actual flat execution. -/
theorem complete_with_fragments
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (afterCaller : Caller width) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧ InputsPending after.core scs ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationReferences.IncomingAvoid held before.core →
        EnumerationReferences.IncomingAvoid held after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
          ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
            Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      (∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
        EnumerationFlatCached.Related flat before →
        ∀ extraNative P H, p ≤ P → h ≤ H →
          ∃ flatResult : SourceFlatPruningSelectedEdge.Result width,
            SourceFlatPruningSelectedEdge.run checkEmpty (n + extraNative) P H
              scs edge caller flat memos.query = flatResult ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatResult result) := by
  obtain ⟨action, own, _prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, ownSafe,
    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  have numeric : SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty inputs caller own memos.query := by
    have admitted := ranges edge.entry.key.symbol _ residual own ownRun
    rwa [readback] at admitted
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    childResult, childrenRun, post, querySame, growth, afterPaths, storage, afterRealized,
    afterCounts, afterFlags, origin, enumProtects, rootsProtects, references, _pendingHistory, fragmentBounds, shape, childrenFlat⟩ :=
    SourceFlatPruningTraversalCompletion.complete_with_fragments formulas solver inventory caller own checkEmpty inputs roots memos
      initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric
  have flatRunning : ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
      EnumerationFlatCached.Related flat before →
      ∀ extraNative P H, p ≤ P → h ≤ H →
        ∃ flatResult : SourceFlatPruningSelectedEdge.Result width,
          SourceFlatPruningSelectedEdge.run checkEmpty (n + extraNative) P H
            scs edge caller flat memos.query = flatResult ∧
          SourceFlatPruningSelectedEdge.ResultRelated flatResult
            (match childResult with
            | .complete children reached saved cache =>
                .complete (.node edge.entry.key.symbol children) reached saved
                  (finish residual (.node edge.entry.key.symbol children) cache)
            | .stopped children observation candidate => .stopped children observation candidate) := by
    intro flat related en P H largeP largeH
    obtain ⟨flatStaged, flatOwn, preparedFlat, stagedInputs, ownRelated, _stages⟩ :=
      SourceFlatPruningCachedOwn.prepare_completed related caller.checked.native.machine.heap
        scs edge edge.entry.key.symbol
        (inputs.map (fun input =>
          (input.1, input.2,
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1)))
        residual own ownRun
    have inputsSame : flatStaged.map (fun input => (input.1, input.2.1)) = inputs :=
      stagedInputs.trans readback
    obtain ⟨flatChildren, flatChildrenRun, compared⟩ :=
      childrenFlat flatOwn ownRelated en P H largeP largeH
    cases childResult with
    | complete children reached saved cache =>
      cases flatChildren with
      | stopped flatFragments observation candidate => exact False.elim compared
      | complete flatFragments flatCaller flatQueries flatCache =>
        obtain ⟨fragmentsSame, callerSame, queriesSame, caches⟩ := compared
        subst flatFragments flatCaller flatQueries
        refine ⟨.complete (.node edge.entry.key.symbol children) reached saved
          (SourceFlatPruningSelectedEdge.finish residual (.node edge.entry.key.symbol children) flatCache),
          ?_, ?_⟩
        · simp only [SourceFlatPruningSelectedEdge.run, preparedFlat]
          rw [inputsSame, flatChildrenRun]
        · exact ⟨rfl, rfl, rfl,
            SourceFlatPruningSelectedEdge.finish_related caches residual (.node edge.entry.key.symbol children)⟩
    | stopped children observation candidate =>
      cases flatChildren with
      | complete flatFragments flatCaller flatQueries flatCache => exact False.elim compared
      | stopped flatFragments flatObservation flatCandidate =>
        refine ⟨.stopped flatFragments flatObservation flatCandidate, ?_, compared⟩
        simp only [SourceFlatPruningSelectedEdge.run, preparedFlat]
        rw [inputsSame, flatChildrenRun]
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have fullOrigin := ownOrigin.trans origin
  have ownPending : InputsPending own.core scs := by
    intro held fragment stored
    have old := ownOrigin held fragment stored
    have frame := EnumerationDriver.suspension_protected held tries.length before.core safe
      (enumerated_root before.core safe held fragment old).1 (enumerated_root before.core safe held fragment old).2
    rw [← ownCore] at frame
    exact frame.avoids scs (pending held fragment old)
  have retained := SourcePruningEnumerationTraversalCompletion.retained_inputs own.core after.core scs
    ownPending origin enumProtects
  have protectedRoots : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core := by
    intro held inside root avoids
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
    exact frame.trans (rootsProtects held (by omega) frame.root avoidsChildren)
  have incomingPreserved : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs → EnumerationReferences.IncomingAvoid held before.core →
      EnumerationReferences.IncomingAvoid held after.core := by
    intro held inside root avoids incoming
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
    have ownAllowed : EnumerationReferences.ReferencesAllowed
        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
      rw [ownCore]
      exact EnumerationReferences.suspension_allowed _ tries.length before.core incoming
    have ownIncoming : EnumerationReferences.IncomingAvoid held own.core := by
      intro value member sc listed same
      exact ownAllowed value member sc listed ((frame.classes sc.var).mp same)
    have allowedAfter := references _ ownIncoming avoidsChildren
    have childFrame := rootsProtects held (by omega) frame.root avoidsChildren
    intro value member sc listed same
    exact allowedAfter value member sc listed ((childFrame.classes sc.var).mp same)
  have pendingPreserved : EnumerationReferences.PendingReferences before.core →
      EnumerationReferences.PendingReferences after.core := by
    intro history held fragment stored
    have old := fullOrigin held fragment stored
    obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment old
    exact incomingPreserved held inside root (pending held fragment old) (history held fragment old)
  rcases shape with ⟨completed, afterSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
  · subst childResult
    let fragment : Fragment := .node edge.entry.key.symbol fragments
    let finished := finish residual fragment after
    have fragmentBound : FragmentBound after.core.counter fragment := node_bound _ _ _ fragmentBounds
    have fragmentPending : PendingFragment after.core fragment :=
      pendingFragment_node after.core _ fragments (fun child member => (fragmentHistory child member).1)
    have fragmentSeparate : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment := by
      intro held inside root avoids uv hole
      obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
      change HasHole (.node edge.entry.key.symbol fragments) uv at hole
      cases hole with
      | child _ _ child _ member below =>
          exact (fragmentHistory child member).2 held (by omega) frame.root avoidsChildren uv below
    refine ⟨r, n, p, h, k, afterCaller, finished, savedQueries, final, next, afterRoots,
      .complete fragment afterCaller savedQueries finished, ?_, post, querySame, ?_, afterPaths,
      (finish_safe residual fragment after afterSafe fragmentBound).1, afterRealized, afterCounts,
      afterFlags, fullOrigin, retained, ?_, pendingPreserved, incomingPreserved, .inl ⟨fragment, rfl,
        finish_safe residual fragment after afterSafe fragmentBound, fragmentBound, fragmentPending, fragmentSeparate⟩, flatRunning⟩
    · intro er en P H ek largeP largeH
      simp only [SourcePruningEnumerationSelectedEdge.run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · change before.core.counter ≤ after.core.counter
      omega
    · intro held inside root avoids
      have frame := protectedRoots held inside root avoids
      exact frame.trans (finish_protected residual fragment after held frame.root)
  · subst childResult
    refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after),
      ?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags,
      fullOrigin, retained, protectedRoots, pendingPreserved, incomingPreserved,
      .inr ⟨fragments, outer, waiting, rfl⟩, flatRunning⟩
    · intro er en P H ek largeP largeH
      simp only [SourcePruningEnumerationSelectedEdge.run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · omega

end MicroCFTA.SourceFlatPruningSelectedCompletion
