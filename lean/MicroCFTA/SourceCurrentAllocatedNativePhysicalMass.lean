import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.InternedValueMassHeap

/-!
# Mass bounds for actual native memo payloads

Physical validity retains complete captured operands in every cell phase.
The current constructor store bounds those operands and returned payloads.
Successful current reads retain the same bound. Initial physical validity
also supplies a computed bound for arbitrary populated native tables.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalMass
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionThunks
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Guard : Type} {width bound : Nat}

/-- Every node phase bounds its captured operands and any returned payload. -/
def NodeMass (bound : Nat)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)) : Prop :=
  InternedValueMass.value cell.request.left ≤ bound ∧
    InternedValueMass.value cell.request.right ≤ bound ∧
    match cell.status with
    | .returned value => InternedValueMass.value value ≤ bound
    | .suspended | .evaluating => True

/-- Every edge phase bounds its complete captured rows and any returned row. -/
def EdgeMass (bound : Nat)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)) : Prop :=
  InternedValueMass.edge cell.request.left ≤ bound ∧
    InternedValueMass.edge cell.request.right ≤ bound ∧
    match cell.status with
    | .returned edge => InternedValueMass.edge edge ≤ bound
    | .suspended | .evaluating => True

/-- An actual node cell uses only current physical validity and the current store bound. -/
theorem node_cell (state : Native width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (stored : Stored bound state.machine.heap) (handle : Nat)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (found : state.nodes.cells handle = some cell) : NodeMass bound cell := by
  have checked := valid.nodes.checked handle cell found
  refine ⟨InternedValueMassHeap.available _ stored _ checked.1.2.1,
    InternedValueMassHeap.available _ stored _ checked.1.2.2, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned value =>
      have available := checked.2
      rw [phase] at available
      exact InternedValueMassHeap.available _ stored value available

/-- An actual edge cell retains the complete row mass in every physical phase. -/
theorem edge_cell (state : Native width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (stored : Stored bound state.machine.heap) (handle : Nat)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (found : state.edges.cells handle = some cell) : EdgeMass bound cell := by
  have checked := valid.edges.checked handle cell found
  refine ⟨InternedValueMassHeap.resident _ stored _ checked.1.2.1,
    InternedValueMassHeap.resident _ stored _ checked.1.2.2, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned edge =>
      have resident := checked.2
      rw [phase] at resident
      exact InternedValueMassHeap.resident _ stored edge resident

/-- Actual current heap records compute one bound for both populated native tables. -/
theorem initial_cells (state : Native width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state) :
    (∀ handle cell, state.nodes.cells handle = some cell →
      NodeMass (InternedValueMassHeap.initialBound state.machine.heap) cell) ∧
    (∀ handle cell, state.edges.cells handle = some cell →
      EdgeMass (InternedValueMassHeap.initialBound state.machine.heap) cell) := by
  have stored := InternedValueMassHeap.initial state.machine.heap valid.machine.1
  exact ⟨fun handle cell found => node_cell state valid stored handle cell found,
    fun handle cell found => edge_cell state valid stored handle cell found⟩

/-- A successful current node read selects an actual payload in the bounded store. -/
theorem read_bound (source : State Symbol Guard) (stored : Stored bound source)
    (identity : Nat) (value : Value Symbol Guard)
    (found : SourcePreparedSharedRows.read source identity = some value) :
    InternedValueMass.value value ≤ bound := by
  obtain ⟨key, _issued, present⟩ := Option.bind_eq_some_iff.mp found
  exact stored.nodes key value present

/-- A successful current edge read uses its own issued map and complete record. -/
theorem edge_read_bound (source : State Symbol Guard) (stored : Stored bound source)
    (identity : Nat) (edge : EdgeValue Symbol Guard)
    (found : SourceRecursiveIntersectionSourceProfile.edgeRead source identity = some edge) :
    InternedValueMass.edge edge ≤ bound := by
  obtain ⟨key, _issued, present⟩ := Option.bind_eq_some_iff.mp found
  exact stored.edges key edge present

/-- One resident row bounds its child-list mass, width, and every child payload. -/
theorem resident_children (source : State Symbol Guard) (stored : Stored bound source)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident source edge) :
    1 + InternedValueMass.values edge.children ≤ bound ∧
      edge.children.length < bound ∧
      ∀ child ∈ edge.children, InternedValueMass.value child < bound := by
  have mass := InternedValueMassHeap.resident source stored edge resident
  rw [InternedValueMass.edge_children] at mass
  have length := InternedValueMass.values_eq_length_sum edge.children
  refine ⟨mass, by omega, ?_⟩
  intro child member
  have smaller := InternedValueMass.value_mem_lt child edge.children member
  omega

end MicroCFTA.SourceCurrentAllocatedNativePhysicalMass
