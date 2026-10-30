import MicroCFTA.SourcePruningEnumerationPathTraversal
import MicroCFTA.SourcePruningEnumerationCapturedEdge
import MicroCFTA.SourcePruningEnumerationHeadAdmission

/-!
# Stored paths at actual completed heads

The actual head preserves the fixed path predicate before callback filtering.
The forecast corollary uses the prepared worker's original admission.
-/
namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationSchedule SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathStorage
local notation "Symbol" => SourcePruningTemplates.Symbol

/-- Finalization stores no suspended references and preserves every other stored path. -/
theorem run_paths {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core)
    (observed : run heap fuel target fragment before = some after) :
    StatePaths P after.core := by
  let reset : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    EnumerationExpandableIndex.frame {before.core with expansionAncestry := []} before
  have resetPaths : StatePaths P reset.core := paths
  change (reset.core.values[target]?).bind (fun old =>
    SourcePruningEnumerationNativeIndex.write heap fuel target (.enumerated fragment)
      [] (references old) reset) = some after at observed
  obtain ⟨old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  apply native_write_paths heap fuel target (.enumerated fragment) [] (references old)
    reset after resetPaths ?_ written
  intro sc member
  simp [references] at member

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}

/-- Residual recording preserves the stored path predicate. -/
theorem finish_paths (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (paths : StatePaths P before.core) : StatePaths P (finish residual fragment before).core :=
  paths

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual completed selected edge preserves the original stored path predicate. -/
theorem complete_paths
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    (completed : run checkEmpty r n p h k scs edge caller before queries =
      .complete fragment reached saved after) : StatePaths P after.core := by
  unfold run at completed
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none => rw [prepared] at completed; cases completed
  | some rows =>
      cases rows with
      | nil => rw [prepared] at completed; cases completed
      | cons row rest =>
          cases rest with
          | cons second rest => rw [prepared] at completed; cases completed
          | nil =>
              obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
              have rowPaths := prepare_paths paths inherited tails projected prepared
                ((symbol, staged, residual), middle) List.mem_cons_self
              have buckets : ∀ input ∈ staged.map (fun input => (input.1, input.2.1)),
                  BucketPaths P input.2 := by
                intro input member
                rcases List.mem_map.mp member with ⟨child, childMember, rfl⟩
                exact rowPaths.2 child childMember
              rw [prepared] at completed
              dsimp only at completed
              cases traversed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped fragments observation candidate =>
                  rw [traversed] at completed
                  cases completed
              | complete fragments selectedCaller selectedQueries selectedCache =>
                  rw [traversed] at completed
                  have selectedPaths := SourcePruningEnumerationChildTraversal.complete_paths
                    checkEmpty r n p h k (staged.map (fun input => (input.1, input.2.1)))
                    caller selectedCaller middle selectedCache queries selectedQueries fragments
                    rowPaths.1 buckets traversed
                  have sameCache : finish residual (.node symbol fragments) selectedCache = after :=
                    (Result.complete.inj completed).2.2.2
                  rw [← sameCache]
                  exact finish_paths residual (.node symbol fragments) selectedCache selectedPaths

end MicroCFTA.SourcePruningEnumerationSelectedEdge

namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual completed captured edge preserves paths through its final write. -/
theorem complete_paths
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    (completed : run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after)) : StatePaths P after.core := by
  unfold run at completed
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k
      scs edge caller before queries with
  | unhandled => rw [selected] at completed; cases completed
  | rejected selectedCaller selectedQueries selectedCache =>
      rw [selected] at completed
      cases completed
  | stopped fragments observation candidate => rw [selected] at completed; cases completed
  | complete produced selectedCaller selectedQueries selectedCache =>
      rw [selected] at completed
      obtain ⟨finished, finishRun, fields⟩ := Option.map_eq_some_iff.mp completed
      have sameCache : finished = after :=
        (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.2.2
      rw [← sameCache]
      apply SourcePruningEnumerationFinalize.run_paths (P := P)
        selectedCaller.checked.native.machine.heap k target produced selectedCache finished ?_ finishRun
      exact SourcePruningEnumerationSelectedEdge.complete_paths checkEmpty r n p h k scs edge
        caller selectedCaller before selectedCache queries selectedQueries produced paths inherited
        tails projected selected

end MicroCFTA.SourcePruningEnumerationCapturedEdge

namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual prepared head retains the same original forecast path predicate. -/
theorem CompletedHeadReceipt.paths_of_forecast
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv handle scs parentEntry storedEdges depth free edge bound fragment reached saved after
      returnedInventory returnedMemos)
    (guards : List Constraint) (P : EqualityTrie.Path → Prop)
    (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (original : StatePaths P before.core) : StatePaths P after.core := by
  have inheritedPaths : BucketPaths P scs :=
    original (.unenumerated (some handle) scs) (List.mem_of_getElem? receipt.admission.stored)
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      receipt.admission.packet.context.ready.semantic.ready.semantic.1.normal.facts.linked
      _ receipt.admission.parentAvailable.resident edge receipt.admission.selected
  have guardIncluded : edge.entry.key.constraint ∈ guards :=
    included (receipt.admission.known edge.entry.key edge resident)
  have completed := receipt.running 0
  simp only [Nat.add_zero] at completed
  apply SourcePruningEnumerationCapturedEdge.complete_paths checkEmpty bound bound bound bound bound
    uv scs edge caller reached before after memos.query saved fragment original inheritedPaths tails
    ?_ completed
  intro tries residual projection
  exact projected edge.entry.key.constraint guardIncluded tries residual projection

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources

namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The ordinary native receipt retains the same original forecast path predicate. -/
theorem CompletedHeadReceipt.paths_of_forecast
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (guards : List Constraint) (P : EqualityTrie.Path → Prop)
    (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (original : StatePaths P before.core) : StatePaths P after.core := by
  obtain ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected⟩ :=
    receipt.admission.source
  have inheritedPaths : BucketPaths P scs :=
    original (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := receipt.admission.packet.valid
  obtain ⟨parent, parentLookup, available, _closed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry storedEdges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      receipt.admission.packet.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (.node parentEntry storedEdges depth free) available.resident edge selected
  have guardIncluded : edge.entry.key.constraint ∈ guards :=
    included (receipt.admission.known edge.entry.key edge resident)
  have completed := receipt.running 0
  simp only [Nat.add_zero] at completed
  apply SourcePruningEnumerationCapturedEdge.complete_paths checkEmpty bound bound bound bound bound
    uv scs edge caller reached before after memos.query saved fragment original inheritedPaths tails
    ?_ completed
  intro tries residual projection
  exact projected edge.entry.key.constraint guardIncluded tries residual projection

end MicroCFTA.SourcePruningEnumerationNativeHookResources
