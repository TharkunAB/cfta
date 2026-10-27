import MicroCFTA.SourcePruningEnumerationCapturedEdgeDiagonalSoundness
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.EnumerationStratifiedTransport
import MicroCFTA.SourcePruningEnumerationSelectedEdgeNeutralSoundness
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Safety and fragment order of diagonal completion

The actual diagonal result identifies the completed native producer.
The same result retains safety and advances its dependency frontier.
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

/-- Actual diagonal completion derives safety and dependency order from the native producer. -/
theorem diagonal_complete_safe_order
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
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    Safe after.core ∧
      ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
  obtain ⟨r, n, p, h, k, reached, finished, saved, final, next, afterRoots, result,
      running, _post, _querySame, _growth, _paths, _storage, _realized, _counts, _flags,
      _origin, _pending, _protects, _pendingHistory, shape⟩ :=
    complete_with_history formulas solver inventory caller before checkEmpty uv handle scs parentEntry edges depth free
      edge roots memos initial ready stored decoded realized selected paths counts flags pending allowed
      tries residual projected ranges
  let w := bound + r + n + p + h + k
  have rl : r ≤ w := by dsimp [w]; omega
  have nl : n ≤ w := by dsimp [w]; omega
  have pl : p ≤ w := by dsimp [w]; omega
  have hl : h ≤ w := by dsimp [w]; omega
  have kl : k ≤ w := by dsimp [w]; omega
  have produced : run checkEmpty w w w w w uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using
      running (w - r) (w - n) w w (w - k) pl hl
  have diagonal : run checkEmpty w w w w w uv scs edge caller before memos.query =
      some (.complete fragment afterCaller savedQueries after) := by
    simpa only [w, Nat.add_assoc] using observed (r + n + p + h + k)
  have same : result = .complete fragment afterCaller savedQueries after :=
    Option.some.inj (produced.symm.trans diagonal)
  rw [same] at shape
  rcases shape with ⟨produced, completed, safe, _bound, _stored, _ancestry, _root, _pendingFragment, ordered⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · cases completed
    exact ⟨safe, ordered⟩
  · cases stopped

end MicroCFTA.SourcePruningEnumerationCapturedEdge
