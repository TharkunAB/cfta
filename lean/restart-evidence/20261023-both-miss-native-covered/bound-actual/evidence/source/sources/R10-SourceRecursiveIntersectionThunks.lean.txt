import MicroCFTA.SourceRecursiveIntersectionEdgeMemo
import MicroCFTA.FlatMemoThunk

/-!
# Source node and edge memo thunk state

Separate typed tables retain original physical requests before evaluation.
Completed cells retain actual guarded kernel execution. This file connects
publication and completed observations. It does not yet run recursive
callbacks through both memo tables.
-/
namespace MicroCFTA.SourceRecursiveIntersectionThunks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel

/-- A node thunk captures the original source domain and ordered operands. -/
structure NodeRequest (Symbol Guard : Type) where
  domain : Interned DomainKey
  left : Value Symbol Guard
  right : Value Symbol Guard

/-- An edge thunk captures the original source domain and ordered physical rows. -/
structure EdgeRequest (Symbol Guard : Type) where
  domain : Interned DomainKey
  left : EdgeValue Symbol Guard
  right : EdgeValue Symbol Guard

/-- Node publication uses the original tagged key and explicit machine bounds. -/
def NodeKey (width : Nat) (request : NodeRequest Symbol Guard) (key : Triple width) : Prop :=
  SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key ∧
    SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right

/-- Edge publication uses raw row identities and explicit machine bounds. -/
def EdgeKeyOf (width : Nat) (request : EdgeRequest Symbol Guard) (key : Triple width) : Prop :=
  SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right = key ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right

/-- Original node inputs stay available while the thunk is suspended or running. -/
def NodeReady (machine : Machine Symbol Guard) (request : NodeRequest Symbol Guard) : Prop :=
  Domain machine request.domain ∧ Available machine.heap request.left ∧ Available machine.heap request.right

/-- Original edge inputs retain their complete resident row records. -/
def EdgeReady (machine : Machine Symbol Guard) (request : EdgeRequest Symbol Guard) : Prop :=
  Domain machine request.domain ∧ EdgeResident machine.heap request.left ∧ EdgeResident machine.heap request.right

/-- Completed node cells have concrete source execution, without a supplied purity law. -/
def NodeGood [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (machine : Machine Symbol Guard) (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)) : Prop :=
  NodeReady machine cell.request ∧ match cell.status with
    | .returned value => SourceRecursiveIntersectionMemo.Produced emptyGuard conjoin machine cell.request.domain cell.request.left cell.request.right value
    | .suspended | .evaluating => True

/-- Completed edge cells have concrete guarded row execution. -/
def EdgeGood [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (machine : Machine Symbol Guard) (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)) : Prop :=
  EdgeReady machine cell.request ∧ match cell.status with
    | .returned value => SourceRecursiveIntersectionEdgeMemo.Produced emptyGuard conjoin machine cell.request.domain cell.request.left cell.request.right value
    | .suspended | .evaluating => True

/-- Source effects and the two native memo families have separate state. -/
structure State (width : Nat) (Symbol Guard : Type) where
  machine : Machine Symbol Guard
  nodes : FlatMemoThunk.State (Triple width) (NodeRequest Symbol Guard) (Value Symbol Guard)
  edges : FlatMemoThunk.State (Triple width) (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)

/-- Every pending request and completed observation retains source provenance. -/
structure Valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) : Prop where
  machine : SourceRecursiveIntersectionKernel.Valid state.machine
  nodes : FlatMemoThunk.Valid (NodeKey width) (NodeGood emptyGuard conjoin state.machine) state.nodes
  edges : FlatMemoThunk.Valid (EdgeKeyOf width) (EdgeGood emptyGuard conjoin state.machine) state.edges

/-- Initialize both memo families without result assumptions. -/
def initial (width : Nat) (machine : Machine Symbol Guard) : State width Symbol Guard := ⟨machine, FlatMemoThunk.empty, FlatMemoThunk.empty⟩

/-- An actual valid source machine admits empty node and edge memo state. -/
theorem initial_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine) :
    Valid width emptyGuard conjoin (initial width machine) :=
  ⟨valid, FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Source node requests with unresolved placeholders bypass the native memo. -/
inductive NodeSelection (Symbol Guard : Type) where
  | direct (request : NodeRequest Symbol Guard)
  | memoized (handle : Nat)

/-- Node lookup publishes a suspended source request and retains the separate edge table. -/
def lookupNode (width : Nat) (request : NodeRequest Symbol Guard) (state : State width Symbol Guard) :
    NodeSelection Symbol Guard × State width Symbol Guard :=
  match SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => (.direct request, state)
  | some key =>
    let (handle, nodes) := FlatMemoThunk.lookupOrInsert key request state.nodes
    (.memoized handle, { state with nodes := nodes })

/-- Edge lookup publishes a suspended original row request in its own family. -/
def lookupEdge (width : Nat) (request : EdgeRequest Symbol Guard) (state : State width Symbol Guard) :
    Nat × State width Symbol Guard :=
  let (handle, edges) := FlatMemoThunk.lookupOrInsert (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) request state.edges
  (handle, { state with edges := edges })

/-- Actual unresolved node keys retain the source direct-call path without memo effects. -/
theorem lookupNode_bypass (width : Nat) (request : NodeRequest Symbol Guard) (state : State width Symbol Guard)
    (unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    lookupNode width request state = (.direct request, state) := by
  simp only [lookupNode, unresolved]

/-- Checked native node publication retains both memo invariants without forcing a value. -/
theorem lookupNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    Valid width emptyGuard conjoin (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some value =>
    have checked := FlatMemoThunk.lookup_valid value request state.nodes (NodeKey width) (NodeGood emptyGuard conjoin state.machine)
      valid.nodes ⟨key, safe⟩ ⟨ready, trivial⟩
    simp only [lookupNode, key]
    exact ⟨valid.machine, checked, valid.edges⟩

/-- Checked native edge publication retains both memo invariants without forcing a row. -/
theorem lookupEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    Valid width emptyGuard conjoin (lookupEdge width request state).2 := by
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.lookup_valid _ request state.edges (EdgeKeyOf width)
    (EdgeGood emptyGuard conjoin state.machine) valid.edges ⟨rfl, safe⟩ ⟨ready, trivial⟩⟩

/-- Native publication uses signed words from the actual checked triple. -/
def publicationKey (key : Triple width) : FlatMemoPublication.Key := ⟨key.1.toInt, key.2.1.toInt, key.2.2.toInt⟩

/-- The actual node key can publish a suspended thunk identity without forcing it. -/
theorem node_publication (width : Nat) (request : NodeRequest Symbol Guard) (key : Triple width) (handle : Nat)
    (checked : NodeKey width request key) :
    FlatMemoPublication.observe (FlatMemoPublication.publish (.prepared (publicationKey key) handle)) = some (publicationKey key, handle) :=
  FlatMemoPublication.publication_exact _ _ (SourceRecursiveIntersectionMemo.requestKey_nonnegative width _ _ _ checked.2 key checked.1)

/-- The actual raw edge key can publish a suspended thunk identity without forcing it. -/
theorem edge_publication (width : Nat) (request : EdgeRequest Symbol Guard) (handle : Nat)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    let key := SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right
    FlatMemoPublication.observe (FlatMemoPublication.publish (.prepared (publicationKey key) handle)) = some (publicationKey key, handle) :=
  FlatMemoPublication.publication_exact _ _ (SourceRecursiveIntersectionEdgeMemo.requestKey_nonnegative width _ _ _ safe)

/-- Completed node observations have the same concrete provenance as the completed-value layer. -/
theorem completed_nodes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state) :
    SourceRecursiveIntersectionMemo.MemoValid width emptyGuard conjoin state.machine (FlatMemoThunk.completed state.nodes) := by
  intro key value stored
  obtain ⟨request, checked, good⟩ := FlatMemoThunk.completed_spec state.nodes (NodeKey width)
    (NodeGood emptyGuard conjoin state.machine) valid.nodes key value stored
  exact ⟨request.domain, request.left, request.right, checked.1, checked.2, good.2⟩

/-- Completed edge observations have the same concrete provenance as the guarded edge layer. -/
theorem completed_edges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state) :
    SourceRecursiveIntersectionEdgeMemo.MemoValid width emptyGuard conjoin state.machine (FlatMemoThunk.completed state.edges) := by
  intro key value stored
  obtain ⟨request, checked, good⟩ := FlatMemoThunk.completed_spec state.edges (EdgeKeyOf width)
    (EdgeGood emptyGuard conjoin state.machine) valid.edges key value stored
  exact ⟨request.domain, request.left, request.right, checked.1, checked.2, good.2⟩

end MicroCFTA.SourceRecursiveIntersectionThunks
