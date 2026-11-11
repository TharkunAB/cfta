import MicroCFTA.SourcePruningEnumerationSharedSelectedEdgeResources
import MicroCFTA.SourcePruningEnumerationSharedChildTraversalModelResources
import MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
import MicroCFTA.EnumerationSemantics

/-!
# A compatible model for one actual shared selected edge

The accepted row derives its own-class plan and residual condition.
The actual child traversal supplies the reached caller, cache and final assignment.
Residual recording retains the filled parent term under that same assignment.
The available ordinary parent need not be the original captured handle's value.
Captured-slot finalization and callbacks remain separate operations.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationOrigins
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The same accepted row derives a complete selected edge, its resource packet and final model. -/
theorem complete_models_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol) (term whole : Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (origin : Origin whole term) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (fragment : Fragment) (extended : Nat → Language.Term Symbol),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
          .complete fragment afterCaller savedQueries after) ∧
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
      Safe after.core ∧ FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended after.core ∧
      Fragments.fill extended fragment = term ∧
      AssignmentOrigins whole after.core.counter extended ∧
      ∀ sc ∈ scs, Suspended.Holds extended term sc := by
  obtain ⟨actualTries, actualResidual, terms, admission, _action, own, ownPacket,
    ownAssignment, ownAgree, _ownBeforeModel, ownModel, _combinedHeld, childModels,
    _ownCost, ownOrigins, childOrigins⟩ :=
    SourcePruningEnumerationOwnChildModelProgress.accepted_own_children_origins
      formulas solver inventory caller before parentEntry edges depth free edge scs roots memos
      initial parentAvailable parentClosed selected safe realized paths counts flags bounded pending
      ambient assignment term satisfied accepted inherited whole old origin
  rcases admission with ⟨ownProjected, _valid, termShape, _childAccepted, _length,
    _allowed, _ownEqualities, residualHeld⟩
  have sameProjection := Option.some.inj (ownProjected.symm.trans projected)
  have sameTries := congrArg Prod.fst sameProjection
  have sameResidual := congrArg Prod.snd sameProjection
  change actualTries = tries at sameTries
  change actualResidual = residual at sameResidual
  subst actualTries
  subst actualResidual
  rcases ownPacket with ⟨_prepared, ownRun, _raw, ownCore, ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, ownProtects⟩
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next,
    afterRoots, extended, childrenRun, post, querySame, growth, afterPaths, storage,
    afterRealized, afterCounts, afterFlags, childrenOrigin, enumProtects, rootsProtects,
    references, _pendingHistory, fragmentBounds, afterSafe, fragmentHistory, returnedFits,
    returnedKnown, childAgree, _childBeforeModel, afterModel, childrenFilled, afterOrigins,
    _finalChildModels⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.complete_models_origins_resources
      seed formulas solver inventory caller own checkEmpty inputs roots memos initial ownSafe
      ownPaths ownCounts ownFlags ownRealized genuine fits reserved known ambient
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      ownAssignment whole terms ownModel childModels ownOrigins childOrigins
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have fullOrigin := ownOrigin.trans childrenOrigin
  have ownPending : InputsPending own.core scs := by
    intro held fragment stored
    have previous := ownOrigin held fragment stored
    have frame := EnumerationDriver.suspension_protected held tries.length before.core safe
      (enumerated_root before.core safe held fragment previous).1
      (enumerated_root before.core safe held fragment previous).2
    rw [← ownCore] at frame
    exact frame.avoids scs (pending held fragment previous)
  have retained := SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.retained_inputs
    own.core after.core scs ownPending childrenOrigin enumProtects
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
    have previous := fullOrigin held fragment stored
    obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment previous
    exact incomingPreserved held inside root (pending held fragment previous) (history held fragment previous)
  let fragment : Fragment := .node edge.entry.key.symbol fragments
  let finished := finish residual fragment after
  have fragmentBound : FragmentBound after.core.counter fragment :=
    node_bound _ _ _ fragmentBounds
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
  have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
    intro uv inside
    exact (childAgree uv (by omega)).trans (ownAgree uv inside)
  have beforeModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended before.core :=
    (state_assignment_congr _ _ before.core safe.1 extended assignment agree).mpr satisfied
  have filled : Fragments.fill extended fragment = term := by
    simpa only [fragment, Fragments.fill, childrenFilled] using termShape.symm
  have residualRun : Success (recordResidual residual fragment) after.core () finished.core := by
    rw [Success, finish_raw]
    simp [finished]
  have finalModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended finished.core :=
    (EnumerationSemantics.recordResidual_assignment _ _ extended residual fragment
      after.core finished.core residualRun).mpr ⟨afterModel, by simpa only [filled] using residualHeld⟩
  have finalHeld : ∀ sc ∈ scs, Suspended.Holds extended term sc := by
    intro sc member path represented
    rw [agree sc.var (bounded sc member)]
    exact inherited sc member path represented
  refine ⟨r, n, p, h, k, afterCaller, finished, savedQueries, final, next, afterRoots,
    fragment, extended, ?_, post, querySame, ?_, afterPaths,
    (finish_safe residual fragment after afterSafe fragmentBound).1,
    afterRealized, afterCounts, afterFlags, fullOrigin, retained, ?_, pendingPreserved,
    incomingPreserved, finish_safe residual fragment after afterSafe fragmentBound,
    fragmentBound, fragmentPending, fragmentSeparate, returnedFits, returnedKnown,
    agree, beforeModel, finalModel, filled, afterOrigins, finalHeld⟩
  · intro er en P H ek largeP largeH
    simp only [run, ownRun]
    rw [readback, childrenRun er en P H ek largeP largeH]
  · change before.core.counter ≤ after.core.counter
    omega
  · intro held inside root avoids
    have frame := protectedRoots held inside root avoids
    exact frame.trans (finish_protected residual fragment after held frame.root)

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
