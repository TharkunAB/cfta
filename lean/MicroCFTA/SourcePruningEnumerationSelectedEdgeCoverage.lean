import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources
import MicroCFTA.SourcePruningEnumerationTraversalCoverage
import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeFinishLanguage
import MicroCFTA.SourcePruningEnumerationAnnotationHeap
import MicroCFTA.EnumerationSuspendedForward

/-!
# Constructive coverage of the actual selected edge

The current annotation heap supplies the exact projected guard meaning.
Fresh witnesses preserve every variable in the original state.
The ordered traversal constructs the accepted children at its own endpoint.
The residual write uses the actual native guard interpretation.
The full original resource packet remains available.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
variable {bits : Nat}

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An accepted selected-edge model constructs the same completed result with all original resources. -/
theorem complete_with_fragments_resources_accepting
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
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
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
      Fits (advance seed (cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient) edge.children terms →
        SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
          (.node edge.entry.key.symbol terms) = true →
        (∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          result = .complete fragment afterCaller savedQueries after ∧
          Fragments.fill extended fragment = .node edge.entry.key.symbol terms ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended after.core := by
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
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    childResult, childrenRun, post, querySame, growth, afterPaths, storage, afterRealized,
    afterCounts, afterFlags, origin, enumProtects, rootsProtects, references, _pendingHistory, fragmentBounds, shape, returnedFits, returnedKnown, childrenAccepting⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting seed formulas solver inventory caller own checkEmpty inputs roots memos
      initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine fits reserved known
  have model : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient) edge.children terms →
      SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
        (.node edge.entry.key.symbol terms) = true →
      (∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →
      ∃ extended : Nat → Language.Term Symbol,
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended before.core ∧
        childResult = .complete fragments afterCaller savedQueries after ∧
        fragments.map (Fragments.fill extended) = terms ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended after.core ∧
        ResidualHolds
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          residual (.node edge.entry.key.symbol terms) := by
    intro ambient assignment terms satisfied accepted guardHolds inherited
    obtain ⟨_validTries, projectionMeaning⟩ :=
      SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
        caller.checked.native.machine.heap parentEntry edges depth free edge
        initial.ready.semantic.ready initial.annotation_heap parentAvailable selected tries residual projected
    obtain ⟨equalities, residualHolds⟩ := (projectionMeaning formulas solver _).mp guardHolds
    obtain ⟨witnesses, ownSatisfied, freshAgree, freshHolds⟩ :=
      fresh_classes_state_complete
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        before.core safe.1 assignment satisfied (.node edge.entry.key.symbol terms) tries equalities
    rw [← ownCore] at ownSatisfied
    have combinedHolds : ∀ sc ∈ scs ++ suspendedVars before.core.counter tries,
        Suspended.Holds witnesses (.node edge.entry.key.symbol terms) sc := by
      intro sc member
      rcases List.mem_append.mp member with old | fresh
      · exact EnumerationConstruction.holds_extension assignment witnesses before.core.counter
          freshAgree sc (bounded sc old) _ (inherited sc old)
      · exact freshHolds sc fresh
    have descended := suspended_descent_forward witnesses edge.entry.key.symbol terms
      (scs ++ suspendedVars before.core.counter tries) combinedHolds
    have indexed : ∀ (nodes : List Node) (values : List (Language.Term Symbol)),
        Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient) nodes values →
        ∀ start,
          (∀ index child, values[index]? = some child →
            ∀ sc ∈ descendScs (start + index) (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) →
          Language.All₂ (fun indexed child =>
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient indexed.1 child ∧
            ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) (nodes.zipIdx start) values := by
      intro nodes values related
      induction related with
      | nil => intro start _; exact .nil
      | cons head tail ih =>
          intro start holds
          simp only [List.zipIdx_cons]
          apply Language.All₂.cons
          · exact ⟨head, by simpa only [Nat.add_zero] using holds 0 _ rfl⟩
          · apply ih (start + 1)
            intro index child found
            have evidence := holds (index + 1) child found
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using evidence
    have indexedModels := indexed edge.children terms accepted 0 (by simpa only [Nat.zero_add] using descended)
    have inputModels : Language.All₂ (fun input term =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds witnesses term sc) inputs terms := by
      have mapped := EnumerationSemantics.all₂_map_both
        (fun indexed : Node × Nat => (indexed.1,
          descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries)))
        id
        (fun indexed child =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient indexed.1 child ∧
          ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars before.core.counter tries),
            Suspended.Holds witnesses child sc)
        (fun input term =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds witnesses term sc)
        (fun _ _ evidence => ⟨evidence.1, by
          simpa only [id_eq, descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]
            using evidence.2⟩)
        edge.children.zipIdx terms indexedModels
      simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.map_id] using mapped
    obtain ⟨extended, childAgree, _ownOriginalSatisfied, completed, filled, afterSatisfied⟩ :=
      childrenAccepting ambient
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        witnesses terms ownSatisfied inputModels
    have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
      intro uv inside
      exact (childAgree uv (by omega)).trans (freshAgree uv inside)
    have originalSatisfied := (state_assignment_congr
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      before.core safe.1 extended assignment agree).mpr satisfied
    exact ⟨extended, agree, originalSatisfied, completed, filled, afterSatisfied, residualHolds⟩
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
    have fragmentBound : FragmentBound after.core.counter fragment := by
      have build : ∀ fragments : List Fragment,
          (∀ child ∈ fragments, FragmentBound after.core.counter child) →
          FragmentBound after.core.counter (.node edge.entry.key.symbol fragments) := by
        intro children childrenBound
        induction children with
        | nil => trivial
        | cons child rest ih =>
            exact ⟨childrenBound child (by simp), ih (fun item member => childrenBound item (by simp [member]))⟩
      exact build fragments fragmentBounds
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
        finish_safe residual fragment after afterSafe fragmentBound, fragmentBound, fragmentPending, fragmentSeparate⟩,
      returnedFits, returnedKnown, ?_⟩
    · intro er en P H ek largeP largeH
      simp only [run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · change before.core.counter ≤ after.core.counter
      omega
    · intro held inside root avoids
      have frame := protectedRoots held inside root avoids
      exact frame.trans (finish_protected residual fragment after held frame.root)
    · intro ambient assignment terms satisfied accepted guardHolds inherited
      obtain ⟨extended, agree, originalSatisfied, _completed, filled, afterSatisfied, residualHolds⟩ :=
        model ambient assignment terms satisfied accepted guardHolds inherited
      have termSame : Fragments.fill extended fragment = .node edge.entry.key.symbol terms := by
        simp only [fragment, Fragments.fill, filled]
      refine ⟨extended, fragment, agree, originalSatisfied, rfl, termSame, ?_⟩
      exact (finish_semantics residual fragment after
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) extended).mpr
        ⟨afterSatisfied, by simpa only [termSame] using residualHolds⟩
  · subst childResult
    refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after),
      ?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags,
      fullOrigin, retained, protectedRoots, pendingPreserved, incomingPreserved,
      .inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, ?_⟩
    · intro er en P H ek largeP largeH
      simp only [run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · omega
    · intro ambient assignment terms satisfied accepted guardHolds inherited
      obtain ⟨extended, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied, _residualHolds⟩ :=
        model ambient assignment terms satisfied accepted guardHolds inherited
      cases impossible

end MicroCFTA.SourcePruningEnumerationSelectedEdge
