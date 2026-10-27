import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.EnumerationStratifiedTransport
import MicroCFTA.SourcePruningEnumerationSelectedEdgeCanonical
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Canonical tries at actual captured-slot completion

The original stored bucket supplies inherited trie validity.
The completed selected edge supplies canonical storage before the final write.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationValidity EnumerationSemantics EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual captured-slot completion derives inherited validity from storage and preserves it. -/
theorem complete_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
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
    (canonical : Canonical before.core)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (completed : run checkEmpty r n p h k uv scs edge caller before memos.query =
      some (.complete fragment afterCaller savedQueries after)) : Canonical after.core := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have inherited : ValidSuspended scs := canonical _ (List.mem_of_getElem? stored)
  unfold run at completed
  cases selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k
      scs edge caller before memos.query with
  | unhandled => simp only [selectedRun, reduceCtorEq] at completed
  | rejected reachedCaller saved reached => simp only [selectedRun, reduceCtorEq] at completed
  | stopped fragments observation candidate => simp only [selectedRun, reduceCtorEq] at completed
  | complete produced reachedCaller saved reached =>
      rw [selectedRun] at completed
      simp only [Option.map_eq_some_iff] at completed
      obtain ⟨finished, finishRun, fields⟩ := completed
      have cacheSame : finished = after := (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.2.2
      rw [← cacheSame]
      exact SourcePruningEnumerationFinalize.run_canonical reachedCaller.checked.native.machine.heap k uv
        produced reached finished
        (SourcePruningEnumerationSelectedEdge.complete_canonical caller before checkEmpty parentEntry edges depth free
          edge scs roots memos initial available closed selected ready.safe realized paths counts flags bounded
          pending allowed tries residual projected canonical inherited selectedRun) finishRun

end MicroCFTA.SourcePruningEnumerationCapturedEdge
