import MicroCFTA.SourcePruningEnumerationPathHead
import MicroCFTA.SourcePruningEnumerationHookInvocation

/-!
# Stored paths at every actual callback input

The selected-edge equation identifies the exact input to each hook.
The original captured cache stays fixed across sibling calls.
-/
namespace MicroCFTA.SourcePruningEnumerationHookInvocation
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual hook input preserves the original path predicate. -/
theorem Invocation.paths
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (edgeProjected : ∀ edge ∈ edges, ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path) :
    StatePaths P after.core := by
  obtain ⟨edge, member, headCaller, headQueries, observed⟩ := invocation.selected
  exact SourcePruningEnumerationCapturedEdge.complete_paths checkEmpty r n p h k target scs edge
    headCaller reached before after headQueries saved fragment paths inherited tails
    (edgeProjected edge member) observed

/-- Initial selected-guard membership supplies the same forecast at every hook input. -/
theorem Invocation.paths_of_forecast
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after)
    (guards : List Constraint)
    (known : ∀ edge ∈ edges, edge.entry.key.constraint ∈ guards)
    (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs) : StatePaths P after.core := by
  apply invocation.paths paths inherited tails
  intro edge member tries residual projection
  exact projected edge.entry.key.constraint (known edge member) tries residual projection

/-- The native input packet supplies paths for every actual hook input. -/
theorem Invocation.paths_of_native_initial
    {Typing : Type}
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target handle depth : Nat} {scs : List Suspended} {before : Cached}
    {storedEdges edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width}
    {memos : EndpointMemoGateTrace.Memos} {saved : Queries} {fragment : Fragment} {after : Cached}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {seed : SourcePruningEnumerationIncomingReservation.Seed}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey} {free : List InternedBinderProtocol.Reference}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller memos.query fragment reached saved after)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (decoded : SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ edges, edge ∈ storedEdges)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (guards : List Constraint) (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) : StatePaths P after.core := by
  have inherited : BucketPaths P scs :=
    paths (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
  obtain ⟨_roots, _rootPaths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨parent, parentLookup, available, _closed⟩ := realized target handle scs stored
  have parentSame : parent = .node parentEntry storedEdges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  apply invocation.paths_of_forecast guards ?_ projected tails paths inherited
  intro edge member
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      packet.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (.node parentEntry storedEdges depth free) available.resident edge (selected edge member)
  exact included (known edge.entry.key edge resident)

/-- The prepared input packet supplies paths for every actual hook input. -/
theorem Invocation.paths_of_prepared_initial
    {Typing : Type}
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target handle depth : Nat} {scs : List Suspended} {before : Cached}
    {storedEdges edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width}
    {memos : EndpointMemoGateTrace.Memos} {saved : Queries} {fragment : Fragment} {after : Cached}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {seed : SourcePruningEnumerationIncomingReservation.Seed}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey} {free : List InternedBinderProtocol.Reference}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller memos.query fragment reached saved after)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentAvailable : InternedProbeProvenance.Available caller.checked.native.machine.heap
      (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ edges, edge ∈ storedEdges)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (guards : List Constraint) (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) : StatePaths P after.core := by
  have inherited : BucketPaths P scs :=
    paths (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
  apply invocation.paths_of_forecast guards ?_ projected tails paths inherited
  intro edge member
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      packet.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (.node parentEntry storedEdges depth free) parentAvailable.resident edge (selected edge member)
  exact included (known edge.entry.key edge resident)

end MicroCFTA.SourcePruningEnumerationHookInvocation
