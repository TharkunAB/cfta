import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources
import MicroCFTA.SourcePruningEnumerationTraversalStoppedProjectionHeap

/-!
# Projection heaps at actual selected-edge returns

The actual own-class prefix supplies each original child admission.
Completed children and outer successful stops retain their reached native heap.
The residual update leaves the native caller unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {bits : Nat}

/-- Original selected-edge admissions preserve projection at actual supported returned callers. -/
theorem run_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
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
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap)
    (r n p h k : Nat) :
    match run checkEmpty r n p h k scs edge caller before memos.query with
    | .complete _ afterCaller _ _ => ProjectionHeap afterCaller.checked.native.machine.heap
    | .stopped _ (.ok _, afterCaller, _, _, _) _ =>
        ProjectionHeap afterCaller.checked.native.machine.heap
    | _ => True := by
  obtain ⟨_action, own, _prepared, ownRun, _raw, _ownCore, _ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  simp only [run, ownRun]
  rw [readback]
  cases traversalRun : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      inputs caller own memos.query with
  | complete fragments afterCaller saved after =>
      have trace := SourcePruningEnumerationChildTraversal.complete_trace checkEmpty r n p h k
        inputs caller afterCaller own after memos.query saved fragments traversalRun
      obtain ⟨_next, _final, _afterRoots, _post, _querySame, _safe, _paths, _counts, _flags,
        _realized, _genuine, _fits, _known, _reserved, projectedAfter⟩ :=
        SourcePruningEnumerationTraversalCompletion.trace_prefix_resources_projection_heap trace [] seed
          formulas solver inventory roots memos rfl initial ownSafe ownPaths ownCounts ownFlags ownRealized
          (by simpa only [List.append_nil] using genuine) fits
          (by simpa only [List.append_nil, cost] using reserved) known originalProjection
      exact projectedAfter
  | stopped fragments observation candidate =>
      rcases observation with ⟨outcome, afterCaller, saved, outer, waiting⟩
      cases outcome with
      | error _fault => trivial
      | ok _raw =>
          exact SourcePruningEnumerationTraversalCompletion.stopped_projection_heap seed formulas solver inventory
            caller own checkEmpty inputs roots memos initial ownSafe ownPaths ownCounts ownFlags ownRealized
            genuine fits reserved known originalProjection traversalRun

end MicroCFTA.SourcePruningEnumerationSelectedEdge
