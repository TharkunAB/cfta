import MicroCFTA.SourceRecursiveIntersectionCompileSafety

/-!
# Exact physical observations of native memo lookup and demand

Native lookup retains the source machine and publishes its actual returned
handle. Demand identifies the original completed cell or its new running
cell. These laws expose operational facts needed by semantic induction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual node lookup changes no physical or domain cache. -/
theorem lookupNode_machine (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (lookupNode width request state).2.machine = state.machine := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right <;> simp only [lookupNode, key]

/-- Actual edge lookup changes no physical or domain cache. -/
theorem lookupEdge_machine (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (lookupEdge width request state).2.machine = state.machine := rfl

/-- Node demand changes only its logical node cell phase. -/
theorem demandNode_machine (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (demandNode handle state).2.machine = state.machine := rfl

/-- Edge demand changes only its logical edge cell phase. -/
theorem demandEdge_machine (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (demandEdge handle state).2.machine = state.machine := rfl

/-- Direct node selection retains the original request and complete native state. -/
theorem lookupNode_direct (request actual : NodeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (selected : lookupNode width request state = (.direct actual, after)) : actual = request ∧ after = state := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | some key => simp only [lookupNode, key] at selected; cases selected
  | none =>
    have same := Prod.mk.inj (by simpa only [lookupNode, key] using selected)
    exact ⟨(NodeSelection.direct.inj same.1).symm, same.2.symm⟩

/-- Memoized node selection derives its actual source key, published handle, and unchanged source machine. -/
theorem lookupNode_memoized (request : NodeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat) (selected : lookupNode width request state = (.memoized handle, after)) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key ∧
      after.nodes.table key = some handle ∧ after.machine = state.machine := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simp only [lookupNode, key] at selected; cases selected
  | some keyValue =>
    have present : (FlatMemoThunk.lookupOrInsert keyValue request state.nodes).2.table keyValue =
        some (FlatMemoThunk.lookupOrInsert keyValue request state.nodes).1 := by
      cases found : state.nodes.table keyValue <;> simp [FlatMemoThunk.lookupOrInsert, found, Cache.put]
    have same := Prod.mk.inj (by simpa only [lookupNode, key] using selected)
    have handles := NodeSelection.memoized.inj same.1
    rcases handles with rfl
    rcases same.2 with rfl
    exact ⟨keyValue, rfl, present, rfl⟩

/-- Edge selection derives its exact raw key and unchanged source machine. -/
theorem lookupEdge_selected (request : EdgeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat) (selected : lookupEdge width request state = (handle, after)) :
    after.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle ∧
      after.machine = state.machine := by
  have present : (FlatMemoThunk.lookupOrInsert (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) request state.edges).2.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) =
        some (FlatMemoThunk.lookupOrInsert (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) request state.edges).1 := by
    cases found : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) <;>
      simp [FlatMemoThunk.lookupOrInsert, found, Cache.put]
  have same := Prod.mk.inj selected
  rcases same.1 with rfl
  rcases same.2 with rfl
  exact ⟨present, rfl⟩

/-- Native node demand derives the exact original completed request and unchanged native state. -/
theorem demandNode_ready (handle : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (ready : demandNode handle state = (.ready value, after)) :
    ∃ request, state.nodes.cells handle = some ⟨request, .returned value⟩ ∧ after = state := by
  cases stored : state.nodes.cells handle with
  | none => simp only [demandNode, FlatMemoThunk.demand, stored] at ready; cases ready
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | evaluating => simp only [demandNode, FlatMemoThunk.demand, stored] at ready; cases ready
      | returned result =>
        have same := Prod.mk.inj (by simpa only [demandNode, FlatMemoThunk.demand, stored] using ready)
        have equal := FlatMemoThunk.Observation.ready.inj same.1
        subst result
        exact ⟨request, rfl, same.2.symm⟩

/-- Native edge demand derives the exact original completed row request and unchanged native state. -/
theorem demandEdge_ready (handle : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : EdgeValue Symbol Guard)
    (ready : demandEdge handle state = (.ready value, after)) :
    ∃ request, state.edges.cells handle = some ⟨request, .returned value⟩ ∧ after = state := by
  cases stored : state.edges.cells handle with
  | none => simp only [demandEdge, FlatMemoThunk.demand, stored] at ready; cases ready
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | evaluating => simp only [demandEdge, FlatMemoThunk.demand, stored] at ready; cases ready
      | returned result =>
        have same := Prod.mk.inj (by simpa only [demandEdge, FlatMemoThunk.demand, stored] using ready)
        have equal := FlatMemoThunk.Observation.ready.inj same.1
        subst result
        exact ⟨request, rfl, same.2.symm⟩

end MicroCFTA.SourceRecursiveIntersectionNative
