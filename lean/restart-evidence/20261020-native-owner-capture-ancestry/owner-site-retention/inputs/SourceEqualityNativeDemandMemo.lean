import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceRecursiveIntersectionNativeShape
import MicroCFTA.FlatMemoThunkReturned

/-!
# Structural memo preservation under checked edge demand

Every observation retains original completed requests and results in both
native families. Publication retains all earlier key-to-handle entries.
Structural validity does not assert completed source provenance. Running
cells can complete, so this relation does not require them to stay running.
-/
namespace MicroCFTA.SourceEqualityNativeDemandMemo
open Cache InternedConstructorTemplates SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionNative

/-- Later native state retains completed cells and all published handles in both families. -/
structure Retained (before after : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  nodes : FlatMemoThunk.Returned before.nodes after.nodes
  edges : FlatMemoThunk.Returned before.edges after.edges
  nodeKeys : Cache.Extends before.nodes.table after.nodes.table
  edgeKeys : Cache.Extends before.edges.table after.edges.table

/-- Unchanged memo state retains every completed cell and key. -/
theorem Retained.refl (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Retained state state :=
  ⟨FlatMemoThunk.Returned.refl _, FlatMemoThunk.Returned.refl _, Cache.extends_refl _, Cache.extends_refl _⟩

/-- Completed-cell and publication retention compose across actual states. -/
theorem Retained.trans (first : Retained before middle) (second : Retained middle after) : Retained before after :=
  ⟨first.nodes.trans second.nodes, first.edges.trans second.edges,
    Cache.extends_trans first.nodeKeys second.nodeKeys, Cache.extends_trans first.edgeKeys second.edgeKeys⟩

private theorem demand_table (handle : Nat) (state : FlatMemoThunk.State Key Request Response) :
    (FlatMemoThunk.demand handle state).2.table = state.table := by
  cases stored : state.cells handle with
  | none => simp only [FlatMemoThunk.demand, stored]
  | some cell => cases cell with
    | mk request status => cases status <;> simp [FlatMemoThunk.demand, stored, FlatMemoThunk.setStatus]

private theorem finish_table (handle : Nat) (value : Response) (state : FlatMemoThunk.State Key Request Response) :
    (FlatMemoThunk.finish handle value state).table = state.table := by
  cases stored : state.cells handle with
  | none => simp [FlatMemoThunk.finish, stored]
  | some cell => cases cell with
    | mk request status => cases status <;> simp [FlatMemoThunk.finish, stored, FlatMemoThunk.setStatus]

/-- Physical and domain effects leave both native memo families unchanged. -/
theorem advance_retained (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard) : Retained state (advance state machine) :=
  ⟨FlatMemoThunk.Returned.refl _, FlatMemoThunk.Returned.refl _, Cache.extends_refl _, Cache.extends_refl _⟩

/-- Original node publication cannot replace an earlier completed cell or handle. -/
theorem lookupNode_retained (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Retained state (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using Retained.refl state
  | some value =>
      simp only [lookupNode, key]
      exact ⟨FlatMemoThunk.lookup_returned value request state.nodes _ shape.1,
        FlatMemoThunk.Returned.refl _, FlatMemoThunk.lookup_extends value request state.nodes,
        Cache.extends_refl _⟩

/-- Original edge publication retains both completed families and all earlier handles. -/
theorem lookupEdge_retained (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (shape : Shape state) : Retained state (lookupEdge width request state).2 :=
  ⟨FlatMemoThunk.Returned.refl _, FlatMemoThunk.lookup_returned _ request state.edges _ shape.2,
    Cache.extends_refl _, FlatMemoThunk.lookup_extends _ request state.edges⟩

/-- Node demand retains every earlier completed cell and publication. -/
theorem demandNode_retained (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retained state (demandNode handle state).2 := by
  refine ⟨FlatMemoThunk.demand_returned _ _, FlatMemoThunk.Returned.refl _, ?_, Cache.extends_refl _⟩
  change Cache.Extends state.nodes.table (FlatMemoThunk.demand handle state.nodes).2.table
  rw [demand_table]
  exact Cache.extends_refl _

/-- Edge demand retains every earlier completed cell and publication. -/
theorem demandEdge_retained (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retained state (demandEdge handle state).2 := by
  refine ⟨FlatMemoThunk.Returned.refl _, FlatMemoThunk.demand_returned _ _, Cache.extends_refl _, ?_⟩
  change Cache.Extends state.edges.table (FlatMemoThunk.demand handle state.edges).2.table
  rw [demand_table]
  exact Cache.extends_refl _

/-- Node completion retains all previous complete results and published handles. -/
theorem finishNode_retained (handle : Nat) (value : Value Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retained state (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  refine ⟨FlatMemoThunk.finish_returned _ _ _, FlatMemoThunk.Returned.refl _, ?_, Cache.extends_refl _⟩
  change Cache.Extends state.nodes.table (FlatMemoThunk.finish handle value state.nodes).table
  rw [finish_table]
  exact Cache.extends_refl _

/-- Edge completion retains all previous complete results and published handles. -/
theorem finishEdge_retained (handle : Nat) (value : EdgeValue Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retained state (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  refine ⟨FlatMemoThunk.Returned.refl _, FlatMemoThunk.finish_returned _ _ _, Cache.extends_refl _, ?_⟩
  change Cache.Extends state.edges.table (FlatMemoThunk.finish handle value state.edges).table
  rw [finish_table]
  exact Cache.extends_refl _

/-- Every original native instruction retains memo structure, prior results, and prior publications. -/
theorem original_step_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code : Code Symbol Guard Output)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (shape : Shape state) :
    Shape (SourceRecursiveIntersectionNative.step emptyGuard conjoin code state).state ∧
      Retained state (SourceRecursiveIntersectionNative.step emptyGuard conjoin code state).state := by
  cases code with
  | pure value | fail failure | read name next => exact ⟨shape, Retained.refl _⟩
  | work job next | enter domain left right first second next => exact ⟨shape, advance_retained _ _⟩
  | optionalBinder key body next =>
      cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap <;>
        simp only [SourceRecursiveIntersectionNative.step, actual, Outcome.state] <;>
        exact ⟨shape, advance_retained _ _⟩
  | finishNode handle value next => exact ⟨finishNode_shape _ _ _ shape, finishNode_retained _ _ _⟩
  | finishEdge handle value next => exact ⟨finishEdge_shape _ _ _ shape, finishEdge_retained _ _ _⟩
  | node request next =>
      have selectedShape := lookupNode_shape request state shape
      have selectedRetained := lookupNode_retained request state shape
      cases selected : lookupNode width request state with
      | mk choice chosen =>
          rw [selected] at selectedShape selectedRetained
          cases choice with
          | direct actual => simpa only [SourceRecursiveIntersectionNative.step, selected, Outcome.state] using ⟨selectedShape, selectedRetained⟩
          | memoized handle =>
              have demandedShape := demandNode_shape handle chosen selectedShape
              have demandedRetained := selectedRetained.trans (demandNode_retained handle chosen)
              cases demanded : demandNode handle chosen with
              | mk observation after =>
                  rw [demanded] at demandedShape demandedRetained
                  cases observation <;> simpa only [SourceRecursiveIntersectionNative.step, selected, demanded, Outcome.state] using ⟨demandedShape, demandedRetained⟩
  | edge request next =>
      have selectedShape := lookupEdge_shape request state shape
      have selectedRetained := lookupEdge_retained request state shape
      cases selected : lookupEdge width request state with
      | mk handle chosen =>
          rw [selected] at selectedShape selectedRetained
          have demandedShape := demandEdge_shape handle chosen selectedShape
          have demandedRetained := selectedRetained.trans (demandEdge_retained handle chosen)
          cases demanded : demandEdge handle chosen with
          | mk observation after =>
              rw [demanded] at demandedShape demandedRetained
              cases observation <;> simpa only [SourceRecursiveIntersectionNative.step, selected, demanded, Outcome.state] using ⟨demandedShape, demandedRetained⟩

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Lifting an original native observation preserves its exact native state. -/
theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (SourceEqualityNativeDemand.lift operations outcome).state.native = outcome.state := by
  cases outcome <;> rfl

/-- Every checked instruction retains structure, prior complete cells, and both publication tables. -/
theorem step_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : SourceEqualityNativeDemand.Control Output) (state : SourceEqualityNativeDemand.State width)
    (shape : Shape state.native) :
    Shape (SourceEqualityNativeDemand.step control state).state.native ∧
      Retained state.native (SourceEqualityNativeDemand.step control state).state.native := by
  cases control with
  | edgeBody request next =>
      simp only [SourceEqualityNativeDemand.step, SourceEqualityNativeDemandOperations.body_native]
      exact ⟨shape, Retained.refl _⟩
  | code code =>
      have delegated := original_step_preserves SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin code state.native shape
      cases code <;> try
        simpa only [SourceEqualityNativeDemand.step, lift_native] using delegated
      rename_i request next
      have selectedShape := lookupEdge_shape request state.native shape
      have selectedRetained := lookupEdge_retained request state.native shape
      cases selected : lookupEdge width request state.native with
      | mk handle chosen =>
          rw [selected] at selectedShape selectedRetained
          have demandedShape := demandEdge_shape handle chosen selectedShape
          have demandedRetained := selectedRetained.trans (demandEdge_retained handle chosen)
          cases demanded : demandEdge handle chosen with
          | mk observation after =>
              rw [demanded] at demandedShape demandedRetained
              cases observation <;> simpa only [SourceEqualityNativeDemand.step, selected, demanded,
                SourceEqualityNativeDemand.Outcome.state] using ⟨demandedShape, demandedRetained⟩

/-- Every finite observation retains both native families, including blocked and error outcomes. -/
theorem execute_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : SourceEqualityNativeDemand.Control Output) (state : SourceEqualityNativeDemand.State width)
    (shape : Shape state.native) :
    Shape (SourceEqualityNativeDemand.execute fuel control state).state.native ∧
      Retained state.native (SourceEqualityNativeDemand.execute fuel control state).state.native := by
  induction fuel generalizing control state with
  | zero => exact ⟨shape, Retained.refl _⟩
  | succ fuel ih =>
      have first := step_preserves control state shape
      cases actual : SourceEqualityNativeDemand.step control state with
      | yielded next after =>
          rw [actual] at first
          have rest := ih next after first.1
          simpa only [SourceEqualityNativeDemand.execute, actual] using ⟨rest.1, first.2.trans rest.2⟩
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual] using first

end MicroCFTA.SourceEqualityNativeDemandMemo
