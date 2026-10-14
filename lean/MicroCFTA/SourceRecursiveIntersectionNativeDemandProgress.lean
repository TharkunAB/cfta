import MicroCFTA.SourceRecursiveIntersectionNativeActiveBounds

/-!
# Native demand progress under derived request bounds

Published handles cannot be absent. A request below all enclosing active
bounds cannot observe busy. Checked machine keys and actual source records
derive exact captured request identity. Active bounds remain an explicit
invariant that the full execution proof must maintain.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode IntersectSchedule

/-- An actually published node handle cannot produce an absent demand. -/
theorem node_absent_impossible (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) (request : NodeRequest Symbol Guard) (handle : Nat)
    (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.absent, current)) : False := by
  have selectedShape : Shape selected := by simpa only [lookup] using lookupNode_shape request state shape
  obtain ⟨key, _, published, _⟩ := lookupNode_memoized request state selected handle lookup
  obtain ⟨cell, stored, _⟩ := selectedShape.1.linked key handle published
  have flat : FlatMemoThunk.demand handle selected.nodes = (.absent, current.nodes) :=
    congrArg (fun actual => (actual.1, actual.2.nodes)) demand
  have missing := FlatMemoThunk.demand_absent_before handle selected.nodes current.nodes flat
  rw [missing] at stored
  cases stored

/-- An actually published edge handle cannot produce an absent demand. -/
theorem edge_absent_impossible (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) (request : EdgeRequest Symbol Guard) (handle : Nat)
    (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.absent, current)) : False := by
  have selectedShape : Shape selected := by simpa only [lookup] using lookupEdge_shape request state shape
  obtain ⟨published, _⟩ := lookupEdge_selected request state selected handle lookup
  obtain ⟨cell, stored, _⟩ := selectedShape.2.linked _ handle published
  have flat : FlatMemoThunk.demand handle selected.edges = (.absent, current.edges) :=
    congrArg (fun actual => (actual.1, actual.2.edges)) demand
  have missing := FlatMemoThunk.demand_absent_before handle selected.edges current.edges flat
  rw [missing] at stored
  cases stored

/-- A checked node request below every enclosing active bound cannot observe its published thunk as busy. -/
theorem node_busy_impossible [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (active : ActiveAbove view holds bound state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (complete : Completes view (nodeSemantic request)) (smaller : requiredFuel view (nodeSemantic request) complete < bound)
    (handle : Nat) (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.busy, current)) : False := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupNode_valid width emptyGuard conjoin state valid request ready safe
  have selectedActive : ActiveAbove view holds bound selected := by
    simpa only [lookup] using active.lookupNode view holds bound state request
  obtain ⟨key, requested, published, machine⟩ := lookupNode_memoized request state selected handle lookup
  have selectedReady : NodeReady selected.machine request := by simpa only [machine] using ready
  have flat : FlatMemoThunk.demand handle selected.nodes = (.busy, current.nodes) :=
    congrArg (fun actual => (actual.1, actual.2.nodes)) demand
  obtain ⟨original, stored, _⟩ := FlatMemoThunk.demand_busy_before handle selected.nodes current.nodes flat
  have same := node_request_exact width emptyGuard conjoin selected selectedValid request selectedReady key
    ⟨requested, safe⟩ handle published ⟨original, .evaluating⟩ stored
  change original = request at same
  subst original
  obtain ⟨actualComplete, bounded⟩ := selectedActive.nodes handle request stored
  exact Nat.not_lt_of_ge bounded smaller

/-- A checked row request below every enclosing active bound cannot observe its published thunk as busy. -/
theorem edge_busy_impossible [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (active : ActiveAbove view holds bound state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (complete : Completes view (edgeSemantic holds request)) (smaller : requiredFuel view (edgeSemantic holds request) complete < bound)
    (handle : Nat) (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.busy, current)) : False := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupEdge_valid width emptyGuard conjoin state valid request ready safe
  have selectedActive : ActiveAbove view holds bound selected := by
    simpa only [lookup] using active.lookupEdge view holds bound state request
  obtain ⟨published, machine⟩ := lookupEdge_selected request state selected handle lookup
  have selectedReady : EdgeReady selected.machine request := by simpa only [machine] using ready
  have flat : FlatMemoThunk.demand handle selected.edges = (.busy, current.edges) :=
    congrArg (fun actual => (actual.1, actual.2.edges)) demand
  obtain ⟨original, stored, _⟩ := FlatMemoThunk.demand_busy_before handle selected.edges current.edges flat
  have same := edge_request_exact width emptyGuard conjoin selected selectedValid request selectedReady _
    ⟨rfl, safe⟩ handle published ⟨original, .evaluating⟩ stored
  change original = request at same
  subst original
  obtain ⟨actualComplete, bounded⟩ := selectedActive.edges handle request stored
  exact Nat.not_lt_of_ge bounded smaller

end MicroCFTA.SourceRecursiveIntersectionNative
