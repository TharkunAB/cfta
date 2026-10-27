import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationTraversalProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationAnnotationHeap

/-!
# Proper pending paths through an actual completed selected edge

The current caller supplies valid projected equality classes.
Actual descent gives valid nonempty inherited and own child buckets.
The same own prefix and completed child trace preserve proper storage.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationSemantics EnumerationProgress Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
/-- Actual child descents have valid nonempty tries from both original input lists. -/
theorem children_proper_inputs
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (start : Nat)
    (tries : List EqualityTrie.Trie) (inherited : ValidSuspended scs)
    (projected : ∀ trie ∈ tries, EqualityTrie.Valid trie) :
    ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      ProperInputs bucket := by
  have own : ValidSuspended (suspendedVars start tries) := by
    intro sc member
    have present : sc.trie ∈ tries := by
      rw [← suspendedVars_tries start tries]
      exact List.mem_map.mpr ⟨sc, member, rfl⟩
    exact projected sc.trie present
  intro incoming bucket member
  obtain ⟨indexed, _present, same⟩ := List.mem_map.mp member
  cases same
  intro sc retained
  rcases List.mem_append.mp retained with inheritedMember | ownMember
  · exact descend_proper scs indexed.2 inherited sc inheritedMember
  · exact descend_proper (suspendedVars start tries) indexed.2 own sc ownMember

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed selected edge preserves proper pending paths. -/
theorem complete_proper
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationProperStateWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (proper : ProperState before.core) (inherited : ValidSuspended scs)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (completed : run checkEmpty r n p h k scs edge caller before memos.query =
      .complete fragment afterCaller savedQueries after) : ProperState after.core := by
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, _ownCounter, _ownForest,
    _ownSafe, _ownPaths, _ownRealized, _ownCounts, _ownFlags, _combinedPending, _genuine,
    _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  have ownProperState : ProperState own.core := by
    rw [ownCore]
    exact suspension_proper tries.length before.core proper
  have triesValid := (SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
    caller.checked.native.machine.heap parentEntry edges depth free edge
    initial.ready.semantic.ready initial.annotation_heap parentAvailable selected tries residual projected).1
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have inputsProper : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket :=
    children_proper_inputs edge scs before.core.counter tries inherited triesValid
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  simp only [run, ownRun] at completed
  rw [readback] at completed
  cases childrenRun : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      inputs caller own memos.query with
  | stopped fragments observation candidate =>
      rw [childrenRun] at completed
      cases completed
  | complete fragments reachedCaller saved reached =>
      rw [childrenRun] at completed
      have same : after = finish residual (.node edge.entry.key.symbol fragments) reached := by
        exact ((Result.complete.inj completed).2.2.2).symm
      rw [same]
      exact finish_proper residual (.node edge.entry.key.symbol fragments) reached
        (SourcePruningEnumerationChildTraversal.complete_proper ownProperState inputsProper childrenRun)

end MicroCFTA.SourcePruningEnumerationSelectedEdge
