import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationTraversalCanonical
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationAnnotationHeap

/-!
# Canonical stored tries through an actual completed selected edge

The current caller supplies valid projected equality classes.
The actual own-class prefix supplies the ordered child input cache.
The actual completed child trace preserves canonical stored buckets.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationSemantics EnumerationValidity Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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

/-- An actual completed selected edge preserves canonical stored suspended tries. -/
theorem complete_canonical
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
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (canonical : Canonical before.core) (inherited : ValidSuspended scs)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (completed : run checkEmpty r n p h k scs edge caller before memos.query =
      .complete fragment afterCaller savedQueries after) : Canonical after.core := by
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, _ownCounter, _ownForest,
    _ownSafe, _ownPaths, _ownRealized, _ownCounts, _ownFlags, _combinedPending, _genuine,
    _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  have ownCanonical : Canonical own.core := by
    rw [ownCore]
    exact suspension_canonical tries.length before.core canonical
  have triesValid := (SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
    caller.checked.native.machine.heap parentEntry edges depth free
    initial.ready.semantic.ready initial.annotation_heap parentAvailable edge selected tries residual projected).1
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have inputsValid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ValidSuspended bucket :=
    SourcePruningEnumerationOrdinarySemanticGates.children_valid edge scs before.core.counter tries
      inherited triesValid
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
      exact finish_canonical residual (.node edge.entry.key.symbol fragments) reached
        (SourcePruningEnumerationChildTraversal.complete_canonical ownCanonical inputsValid childrenRun)

end MicroCFTA.SourcePruningEnumerationSelectedEdge
