import MicroCFTA.InternedValueMassConstructors
import MicroCFTA.InternedFreshOrdinaryResultMass
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

/-!
# Payload and allocation bounds for literal query constructor work

The bounds apply to the actual node, edge, and union constructors.
Each input list has a literal length. Current available inputs supply its
element bounds. Earlier stored winners remain in the same causal bound.
These local bounds do not construct a complete recursive query.
-/
namespace MicroCFTA.SourceRecursiveIntersectionWorkMass
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedValueMassHeap (Stored)
open InternedFreshOrdinaryResultMass (inflate)
open SourceCurrentAllocatedFiniteOrdinaryReservations
variable {Symbol Guard : Type} {bound width : Nat}

/-- Bound the complete ordered value list from its literal length and element bounds. -/
theorem values_le (values : List (Value Symbol Guard)) (bound : Nat)
    (small : ∀ value ∈ values, InternedValueMass.value value ≤ bound) :
    InternedValueMass.values values ≤ values.length * (1 + bound) := by
  induction values with
  | nil => simp only [InternedValueMass.values, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := small first List.mem_cons_self
      have tail := ih (fun value member => small value (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.values, List.length_cons, Nat.succ_mul]
      omega

/-- Bound the complete ordered row list from its literal length and element bounds. -/
theorem edges_le (rows : List (EdgeValue Symbol Guard)) (bound : Nat)
    (small : ∀ row ∈ rows, InternedValueMass.edge row ≤ bound) :
    InternedValueMass.edges rows ≤ rows.length * (1 + bound) := by
  induction rows with
  | nil => simp only [InternedValueMass.edges, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := small first List.mem_cons_self
      have tail := ih (fun row member => small row (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.edges, List.length_cons, Nat.succ_mul]
      omega

/-- A larger literal list limit retains the same common store bound. -/
theorem inflate_width {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    inflate first bound ≤ inflate last bound := by
  have multiplied := Nat.mul_le_mul_right (1 + bound) enough
  unfold inflate
  omega

section Constructors
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Literal edge work derives its store, returned payload, and identity charges. -/
theorem edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (stored : Stored bound before)
    (small : ∀ value ∈ values, InternedValueMass.value value ≤ bound) :
    Stored (inflate values.length bound) (run (makeEdge symbol guard values) before).2 ∧
      InternedValueMass.edge (run (makeEdge symbol guard values) before).1 ≤ inflate values.length bound ∧
      (run (makeEdge symbol guard values) before).2.nodes.next = before.nodes.next ∧
      (run (makeEdge symbol guard values) before).2.edges.next ≤ before.edges.next + 1 := by
  have actual := InternedValueMassConstructors.edge symbol guard values before stored
  have mass := values_le values bound small
  have increase : max bound (1 + InternedValueMass.values values) ≤ inflate values.length bound := by
    unfold inflate
    omega
  have counters := makeEdge_next symbol guard values before
  exact ⟨actual.1.mono increase, Nat.le_trans actual.2 increase, counters⟩

/-- Literal node work derives its store, returned payload, and identity charges. -/
theorem node (rows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (stored : Stored bound before) (small : ∀ row ∈ rows, InternedValueMass.edge row ≤ bound) :
    Stored (inflate rows.length bound) (run (makeNode rows) before).2 ∧
      InternedValueMass.value (run (makeNode rows) before).1 ≤ inflate rows.length bound ∧
      (run (makeNode rows) before).2.nodes.next ≤ before.nodes.next + 1 ∧
      (run (makeNode rows) before).2.edges.next = before.edges.next := by
  have actual := InternedValueMassConstructors.node rows before stored
  have mass := edges_le rows bound small
  have increase : max bound (1 + InternedValueMass.edges rows) ≤ inflate rows.length bound := by
    unfold inflate
    omega
  have counters := makeNode_next rows before
  exact ⟨actual.1.mono increase, Nat.le_trans actual.2 increase, counters⟩

/-- Union flattening and either final constructor path use at most one node request. -/
theorem union_requests (values : List (Value Symbol Guard)) (before : State Symbol Guard) :
    nodeRequests (observe (makeUnion values) before) ≤ 1 ∧
      edgeRequests (observe (makeUnion values) before) = 0 := by
  unfold makeUnion
  generalize chosen : distinctNodes (values.flatMap unionMembers) = members
  cases members with
  | nil => exact ⟨Nat.zero_le _, rfl⟩
  | cons first rest =>
      cases rest with
      | nil => exact ⟨Nat.zero_le _, rfl⟩
      | cons second tail =>
          dsimp only
          split
          · rename_i rows found
            have actual := makeNode_requests rows before
            refine ⟨?_, actual.2⟩
            rw [actual.1]
            split <;> omega
          · exact ⟨Nat.le_refl _, rfl⟩

/-- Literal union work derives its store, returned payload, and identity charges. -/
theorem union (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (stored : Stored bound before) (small : ∀ value ∈ values, InternedValueMass.value value ≤ bound) :
    Stored (inflate values.length bound) (run (makeUnion values) before).2 ∧
      InternedValueMass.value (run (makeUnion values) before).1 ≤ inflate values.length bound ∧
      (run (makeUnion values) before).2.nodes.next ≤ before.nodes.next + 1 ∧
      (run (makeUnion values) before).2.edges.next = before.edges.next := by
  have actual := InternedValueMassConstructors.union values before stored
  have mass := values_le values bound small
  have increase : max bound (1 + InternedValueMass.values values) ≤ inflate values.length bound := by
    unfold inflate
    omega
  have counts := union_requests values before
  have counters := run_next_le (makeUnion values) before
  have exactCounts := run_next (makeUnion values) before
  have reserved := reservations_le_requests (observe (makeUnion values) before)
  exact ⟨actual.1.mono increase, Nat.le_trans actual.2 increase, by omega, by omega⟩

end Constructors

/-- Current physical constructor inputs retain their literal list limit. -/
inductive Inputs (width : Nat) (before : State Symbol Guard) : {A : Type} → Work Symbol Guard A → Prop where
  /-- Pure work changes no store or identity counter. -/
  | pure (value : A) : Inputs width before (.pure value)
  /-- Edge work retains its literal available children and their count. -/
  | edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
      (available : ∀ value ∈ values, Available before value) (length : values.length ≤ width) :
      Inputs width before (makeEdge symbol guard values)
  /-- Node work retains its literal resident rows and their count. -/
  | node (rows : List (EdgeValue Symbol Guard))
      (resident : ∀ row ∈ rows, EdgeResident before row) (length : rows.length ≤ width) :
      Inputs width before (makeNode rows)
  /-- Union work retains its literal available members and their count. -/
  | union (values : List (Value Symbol Guard))
      (available : ∀ value ∈ values, Available before value) (length : values.length ≤ width) :
      Inputs width before (makeUnion values)

/-- Bounded physical inputs supply the original source Work input check. -/
theorem Inputs.physical {before : State Symbol Guard} {job : Work Symbol Guard A}
    (inputs : Inputs width before job) : SourceEqualityNativeDemandHeapPrimitives.WorkInputs before job := by
  cases inputs with
  | pure value => exact .pure value
  | edge symbol guard values available length => exact .edge symbol guard values available
  | node rows resident length => exact .node rows resident
  | union values available length => exact .union values available

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every literal checked constructor retains the causal store and consumes at most one identity. -/
theorem run_bound {before : State Symbol Guard} {job : Work Symbol Guard A}
    (stored : Stored bound before) (inputs : Inputs width before job) :
    Stored (inflate width bound) (run job before).2 ∧
      (run job before).2.nodes.next ≤ before.nodes.next + 1 ∧
      (run job before).2.edges.next ≤ before.edges.next + 1 := by
  cases inputs with
  | pure value =>
      refine ⟨stored.mono (InternedFreshOrdinaryResultMass.inflate_ge width bound), ?_, ?_⟩ <;>
        simp only [run] <;> omega
  | edge symbol guard values available length =>
      have actual := edge symbol guard values before stored
        (fun value member => InternedValueMassHeap.available before stored value (available value member))
      exact ⟨actual.1.mono (inflate_width length bound), by omega, actual.2.2.2⟩
  | node rows resident length =>
      have actual := node rows before stored
        (fun row member => InternedValueMassHeap.resident before stored row (resident row member))
      exact ⟨actual.1.mono (inflate_width length bound), actual.2.2.1, by omega⟩
  | union values available length =>
      have actual := union values before stored
        (fun value member => InternedValueMassHeap.available before stored value (available value member))
      exact ⟨actual.1.mono (inflate_width length bound), actual.2.2.1, by omega⟩

end MicroCFTA.SourceRecursiveIntersectionWorkMass
