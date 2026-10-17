import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
import MicroCFTA.SourceCurrentOperationGrowth
import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Equality-operation invariants from actual native returns

Physical native cells retain resident inputs and results. Their invariant
uses no machine word bound and no semantic result law. Actual completed
compiled calls derive their operation-cache invariants from initial fields.
-/
namespace MicroCFTA.SourceCurrentNativeOperationInvariants
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCache (NodeGood EdgeGood)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Operands" => SourceCurrentAllocatedNativeCodeProgress.Operands
local notation "Fields" => SourceCurrentConjunctionEquality.Fields
variable {width : Nat}
/-- Physical validity includes exact original keys, fresh handles, and resident results. -/
private structure Cells (state : Native width Symbol Guard) : Prop where
  machine : SourceRecursiveIntersectionKernel.Valid state.machine
  nodes : FlatMemoThunk.Valid (fun _ _ => True) (NodeGood state.machine) state.nodes
  edges : FlatMemoThunk.Valid (fun _ _ => True) (EdgeGood state.machine) state.edges

/-- An actual valid machine admits empty physical memo tables. -/
private theorem initial_valid (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) : Cells (initial width machine) :=
  ⟨valid, FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Actual machine growth retains both checked memo families and their original inputs. -/
private theorem advance_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (after : Machine Symbol Guard) (checked : SourceRecursiveIntersectionKernel.Valid after)
    (growth : Extension state.machine after) : Cells (advance state after) :=
  ⟨checked, FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun _ good => good.grows growth),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun _ good => good.grows growth)⟩

/-- Node publication checks current original inputs and the source word range. -/
private theorem lookupNode_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    :
    Cells (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some value =>
      simp only [lookupNode, key]
      exact ⟨valid.machine, FlatMemoThunk.lookup_valid value request state.nodes _ _ valid.nodes
        trivial ⟨ready, trivial⟩, valid.edges⟩

/-- Edge publication checks complete current rows and their original source word range. -/
private theorem lookupEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    :
    Cells (lookupEdge width request state).2 :=
  ⟨valid.machine, valid.nodes, FlatMemoThunk.lookup_valid _ request state.edges _ _ valid.edges
    trivial ⟨ready, trivial⟩⟩

/-- Node demand retains every original input and returned availability. -/
private theorem demandNode_valid
    (state : Native width Symbol Guard) (valid : Cells state) (handle : Nat) :
    Cells (demandNode handle state).2 := by
  cases stored : state.nodes.cells handle with
  | none => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid
  | some cell =>
      have good := valid.nodes.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid
          | suspended =>
              simp only [demandNode, FlatMemoThunk.demand, stored]
              exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle .evaluating state.nodes _ _
                valid.nodes _ stored ⟨good.1, trivial⟩, valid.edges⟩

/-- Edge demand retains both native families and every returned row residency. -/
private theorem demandEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state) (handle : Nat) :
    Cells (demandEdge handle state).2 := by
  cases stored : state.edges.cells handle with
  | none => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid
  | some cell =>
      have good := valid.edges.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid
          | suspended =>
              simp only [demandEdge, FlatMemoThunk.demand, stored]
              exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle .evaluating state.edges _ _
                valid.edges _ stored ⟨good.1, trivial⟩⟩

/-- Completion stores an available value at its original running node handle. -/
private theorem finishNode_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap value) :
    Cells (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  have good := valid.nodes.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle (.returned value) state.nodes _ _
    valid.nodes _ running ⟨good.1, available⟩, valid.edges⟩

/-- Completion stores a resident row at its original running edge handle. -/
private theorem finishEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.machine.heap value) :
    Cells (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  have good := valid.edges.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle (.returned value) state.edges _ _
    valid.edges _ running ⟨good.1, resident⟩⟩


end MicroCFTA.SourceCurrentNativeOperationInvariants
