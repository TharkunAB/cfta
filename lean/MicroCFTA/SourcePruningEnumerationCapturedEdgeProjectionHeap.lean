import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeProjectionHeap

/-!
# Projection heaps through actual captured finalization

The original captured input derives the selected edge's admissions.
Finalization writes the enumeration cache and retains the native caller.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
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

/-- Actual supported captured returns retain projection from their original caller. -/
theorem run_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap)
    (r n p h k : Nat) :
    match run checkEmpty r n p h k uv scs edge caller before memos.query with
    | some (.complete _ afterCaller _ _) => ProjectionHeap afterCaller.checked.native.machine.heap
    | some (.stopped _ (.ok _, afterCaller, _, _, _) _) =>
        ProjectionHeap afterCaller.checked.native.machine.heap
    | _ => True := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have selectedProjection := SourcePruningEnumerationSelectedEdge.run_projection_heap seed formulas solver
    inventory caller before checkEmpty parentEntry edges depth free edge scs roots memos initial available
    closed selected ready.safe realized paths counts flags bounded pending allowed tries residual projected
    fits reserved known originalProjection r n p h k
  unfold run
  cases selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge
      caller before memos.query with
  | unhandled => trivial
  | rejected _ _ _ => trivial
  | stopped completedPrefix observation candidate =>
      rcases observation with ⟨outcome, reached, saved, outer, waiting⟩
      cases outcome with
      | error _fault => trivial
      | ok _raw => simpa only [selectedRun] using selectedProjection
  | complete fragment reached saved middle =>
      have reachedProjection : ProjectionHeap reached.checked.native.machine.heap := by
        simpa only [selectedRun] using selectedProjection
      cases finished : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k uv fragment middle with
      | none => simp only [finished, Option.map_none]
      | some after => simpa only [finished, Option.map_some] using reachedProjection

end MicroCFTA.SourcePruningEnumerationCapturedEdge
