import MicroCFTA.SourcePruningEnumerationSelectedEdgeSoundness
import MicroCFTA.SourcePruningEnumerationAnnotationHeap
import MicroCFTA.SourcePruningEnumerationCheckedBuildArity
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates

/-!
# Selected-edge soundness from actual current caller invariants

The original Context supplies the current normalized annotation heap.
Valid inherited tries give valid actual child buckets.
An actual checked constructor receipt can supply the fresh arity gate.
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

/-- Current Context derives annotations and actual child validity for completed-edge soundness. -/
theorem stable_complete_sound_current
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
    (inheritedValid : EnumerationSemantics.ValidSuspended scs)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
        .complete fragment afterCaller savedQueries after) :
    (∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      EnumerationSemantics.ValidSuspended bucket) ∧
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (Fragments.fill assignment fragment) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (Fragments.fill assignment fragment) ∧
      ∀ sc ∈ scs, Suspended.Holds assignment (Fragments.fill assignment fragment) sc := by
  obtain ⟨valid, _guardMeaning⟩ := SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
    caller.checked.native.machine.heap parentEntry edges depth free edge initial.ready.semantic.ready
      initial.annotation_heap parentAvailable selected tries residual projected
  refine ⟨SourcePruningEnumerationOrdinarySemanticGates.children_valid edge scs before.core.counter
    tries inheritedValid valid, ?_⟩
  exact stable_complete_sound formulas solver inventory caller before checkEmpty parentEntry edges depth free
    edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
      bounded pending allowed tries residual projected ranges initial.annotation_heap inheritedValid
      nonterminal freshArity retained observed

/-- An actual checked return also derives fresh arity for the selected edge at the current caller. -/
theorem stable_complete_sound_checked_build
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
    (inheritedValid : EnumerationSemantics.ValidSuspended scs)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (sourceSymbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (sourceChildren : List Node) (operations : SourceEqualityConstraintMemoAllocation.State)
    (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready operations.constraints stored)
    (validOperations : SourceEqualityConstraintMemoAllocation.Valid operations)
    (sourceReady : SourceEqualityRequiredCache.Ready sourceHeap)
    (sourceAvailable : SourceEqualityMkEdgeAllocation.accepted original sourceChildren.length = true →
      InternedNestedProvenance.Values sourceHeap sourceChildren)
    (builtOperations : SourceEqualityConstraintMemoAllocation.State)
    (builtHeap : InternedConstructorTemplates.State Symbol Constraint)
    (constructed : SourceEqualityMkEdgeAllocation.build sourceSymbol stored original.guard sourceChildren
      operations sourceHeap = (.ok edge, builtOperations, builtHeap))
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
        .complete fragment afterCaller savedQueries after) :
    (∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      EnumerationSemantics.ValidSuspended bucket) ∧
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (Fragments.fill assignment fragment) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (Fragments.fill assignment fragment) ∧
      ∀ sc ∈ scs, Suspended.Holds assignment (Fragments.fill assignment fragment) sc := by
  have own := SourcePruningEnumerationCheckedBuildArity.observed_projected_arity
    sourceSymbol original stored sourceChildren operations sourceHeap cached physical storedReady
      validOperations sourceReady sourceAvailable edge builtOperations builtHeap constructed tries residual projected
  exact stable_complete_sound_current formulas solver inventory caller before checkEmpty parentEntry edges depth free
    edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
      bounded pending allowed tries residual projected ranges inheritedValid nonterminal (own.2 before.core.counter)
      retained observed

end MicroCFTA.SourcePruningEnumerationSelectedEdge
