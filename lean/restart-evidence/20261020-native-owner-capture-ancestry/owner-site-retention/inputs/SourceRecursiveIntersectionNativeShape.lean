import MicroCFTA.SourceRecursiveIntersectionBodyCode
import MicroCFTA.FlatMemoThunkRunning

/-!
# Native memo structure and retained running requests

The structural invariant records fresh handles and original request keys.
It does not assert physical input availability, machine word injectivity,
or completed source provenance. Both memo families retain running requests
through lookup, demand, and source machine effects.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Node cell links retain the original source machine triple without an injectivity assertion. -/
def NodeLink (width : Nat) (request : NodeRequest Symbol Guard) (key : Triple width) : Prop :=
  SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key

/-- Edge cell links retain the original ordered raw row triple. -/
def EdgeLink (width : Nat) (request : EdgeRequest Symbol Guard) (key : Triple width) : Prop :=
  SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right = key

/-- Native memo structure does not assume a semantic completed-value invariant. -/
def Shape (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  FlatMemoThunk.Valid (NodeLink width) (fun _ => True) state.nodes ∧ FlatMemoThunk.Valid (EdgeLink width) (fun _ => True) state.edges

/-- Both source memo families retain every original running request. -/
def Retains (before after : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  FlatMemoThunk.Running before.nodes after.nodes ∧ FlatMemoThunk.Running before.edges after.edges

/-- Unchanged source state retains every running request in both families. -/
theorem Retains.refl (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Retains state state :=
  ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.Running.refl _⟩

/-- Running request retention composes through actual source states. -/
theorem Retains.trans (first : Retains before middle) (second : Retains middle after) : Retains before after :=
  ⟨first.1.trans second.1, first.2.trans second.2⟩

/-- Complete source provenance implies the weaker memo structure used in lifecycle induction. -/
theorem shape_of_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) : Shape state := by
  constructor
  · refine ⟨valid.nodes.bounded, ?_, fun _ _ _ => trivial⟩
    intro key handle stored
    obtain ⟨cell, present, linked⟩ := valid.nodes.linked key handle stored
    exact ⟨cell, present, linked.1⟩
  · refine ⟨valid.edges.bounded, ?_, fun _ _ _ => trivial⟩
    intro key handle stored
    obtain ⟨cell, present, linked⟩ := valid.edges.linked key handle stored
    exact ⟨cell, present, linked.1⟩

/-- Source node lookup retains structural validity without assuming a completed result. -/
theorem lookupNode_shape (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Shape (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using shape
  | some value =>
    simp only [lookupNode, key]
    exact ⟨FlatMemoThunk.lookup_valid value request state.nodes _ _ shape.1 key trivial, shape.2⟩

/-- Source edge lookup retains structural validity without assuming a completed result. -/
theorem lookupEdge_shape (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Shape (lookupEdge width request state).2 :=
  ⟨shape.1, FlatMemoThunk.lookup_valid _ request state.edges _ _ shape.2 rfl trivial⟩

/-- Node demand retains original request links through every cell phase. -/
theorem demandNode_shape (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (shape : Shape state) :
    Shape (demandNode handle state).2 := ⟨FlatMemoThunk.demand_valid _ _ _ shape.1, shape.2⟩

/-- Edge demand retains original request links through every cell phase. -/
theorem demandEdge_shape (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (shape : Shape state) :
    Shape (demandEdge handle state).2 := ⟨shape.1, FlatMemoThunk.demand_valid _ _ _ shape.2⟩

/-- Node publication retains all already-running source requests. -/
theorem lookupNode_retains (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Retains state (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using Retains.refl state
  | some value =>
    simp only [lookupNode, key]
    exact ⟨FlatMemoThunk.lookup_running value request state.nodes _ shape.1, FlatMemoThunk.Running.refl _⟩

/-- Edge publication retains all already-running source requests. -/
theorem lookupEdge_retains (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Retains state (lookupEdge width request state).2 :=
  ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.lookup_running _ request state.edges _ shape.2⟩

/-- Node demand does not reset an enclosing running node or edge request. -/
theorem demandNode_retains (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains state (demandNode handle state).2 := ⟨FlatMemoThunk.demand_running _ _, FlatMemoThunk.Running.refl _⟩

/-- Edge demand does not reset an enclosing running node or edge request. -/
theorem demandEdge_retains (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains state (demandEdge handle state).2 := ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.demand_running _ _⟩

/-- Node completion preserves the original structural key and handle invariant. -/
theorem finishNode_shape (handle : Nat) (value : Value Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Shape (SourceRecursiveIntersectionThunks.finishNode handle value state) :=
  ⟨FlatMemoThunk.finish_valid _ _ _ _ shape.1, shape.2⟩

/-- Edge completion preserves the original structural key and handle invariant. -/
theorem finishEdge_shape (handle : Nat) (value : EdgeValue Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Shape (SourceRecursiveIntersectionThunks.finishEdge handle value state) :=
  ⟨shape.1, FlatMemoThunk.finish_valid _ _ _ _ shape.2⟩

/-- Source node demand identifies its exact original suspended and returned running cells. -/
theorem demandNode_evaluate (handle : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (request : NodeRequest Symbol Guard)
    (started : demandNode handle state = (.evaluate request, after)) :
    state.nodes.cells handle = some ⟨request, .suspended⟩ ∧ after.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  have raw := congrArg (fun result => (result.1, result.2.nodes)) started
  exact FlatMemoThunk.demand_evaluate handle state.nodes after.nodes request raw

/-- Source edge demand identifies its exact original suspended and returned running cells. -/
theorem demandEdge_evaluate (handle : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (started : demandEdge handle state = (.evaluate request, after)) :
    state.edges.cells handle = some ⟨request, .suspended⟩ ∧ after.edges.cells handle = some ⟨request, .evaluating⟩ := by
  have raw := congrArg (fun result => (result.1, result.2.edges)) started
  exact FlatMemoThunk.demand_evaluate handle state.edges after.edges request raw

end MicroCFTA.SourceRecursiveIntersectionNative
