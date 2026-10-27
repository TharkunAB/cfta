import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEdgeFinishLanguage
import MicroCFTA.SourcePruningEnumerationTraversalLanguage

/-!
# Exact assignment restrictions of a completed selected edge

The actual own-class prefix supplies the traversal input cache.
Common bounds align the actual complete edge with a canonical traversal.
The final cache records the residual at the actual returned fragment.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed edge has exactly its effective child restrictions and retained residual. -/
theorem stable_complete_semantics
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
    (ranges : Ranges checkEmpty scs edge caller before memos.query)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
        .complete fragment afterCaller savedQueries after) :
    ∃ childFragments : List Fragment,
      fragment = .node edge.entry.key.symbol childFragments ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core ∧
        All₂ (fun (input : Node × List Suspended) (child : Fragment) =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient input.1 (Fragments.fill assignment child) ∧
          ∀ sc ∈ (match input.1 with
            | .node _ _ _ _ => input.2
            | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
            Suspended.Holds assignment (Fragments.fill assignment child) sc)
          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) childFragments ∧
        ResidualHolds residualMeaning residual (Fragments.fill assignment fragment) := by
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, _ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine,
    _ownProtects⟩ :=
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
  obtain ⟨childR, childN, childP, childH, childK, childFragments, reachedCaller,
    reached, childQueries, _childMemos, _childInventory, _childRoots, childResult,
    childrenRun, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _enumProtects, _rootsProtects, _references,
    _pendingHistory, _fragmentBounds, shape, childMeaning⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_semantics
      formulas solver inventory caller own checkEmpty inputs roots memos
      initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric
  have commonRun := observed childR childN (max p childP) (max h childH) childK
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have childrenAt : SourcePruningEnumerationChildTraversal.run checkEmpty
      (r + childR) (n + childN) (max p childP) (max h childH) (k + childK)
      inputs caller own memos.query = childResult := by
    simpa only [Nat.add_comm] using childrenRun r n (max p childP) (max h childH) k
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rcases shape with ⟨completed, _afterSafe, _fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
  · rw [completed] at childrenAt
    have canonicalRun : run checkEmpty (r + childR) (n + childN) (max p childP) (max h childH)
        (k + childK) scs edge caller before memos.query =
        .complete (.node edge.entry.key.symbol childFragments) reachedCaller childQueries
          (finish residual (.node edge.entry.key.symbol childFragments) reached) := by
      simp only [run, ownRun]
      rw [readback, childrenAt]
    have fields : fragment = .node edge.entry.key.symbol childFragments ∧
        afterCaller = reachedCaller ∧ savedQueries = childQueries ∧
        after = finish residual (.node edge.entry.key.symbol childFragments) reached := by
      simpa only [Result.complete.injEq] using commonRun.symm.trans canonicalRun
    obtain ⟨fragmentSame, callerSame, _queriesSame, cacheSame⟩ := fields
    refine ⟨childFragments, fragmentSame, ?_⟩
    intro ambient residualMeaning assignment
    rw [cacheSame, callerSame, fragmentSame]
    have ownMeaning :
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment own.core ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core := by
      rw [ownCore]
      exact suspendMany_semantics _ residualMeaning assignment tries.length before.core safe.1.aligned
    rw [finish_semantics residual (.node edge.entry.key.symbol childFragments) reached
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reachedCaller.checked.native.machine.heap) residualMeaning assignment,
      childMeaning completed ambient residualMeaning assignment, ownMeaning]
    exact and_assoc
  · rw [stopped] at childrenAt
    simp only [run, ownRun] at commonRun
    rw [readback, childrenAt] at commonRun
    cases commonRun

end MicroCFTA.SourcePruningEnumerationSelectedEdge
