import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceRecursiveIntersectionCompile
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile

/-!
# Mass bounds for actual compiled row and union suffixes

Original row and member occurrences bound the emitted request counts.
Completed ordered walks supply their exact returned lists and machines.
A causal store bound at that prefix bounds the final constructor. These
local assemblers do not produce the recursive calls' store preservation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCompileMass
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Stored" => InternedValueMassHeap.Stored
local notation "inflate" => InternedFreshOrdinaryResultMass.inflate
variable {Symbol Guard : Type}

/-- Every original child occurrence contributes to its complete list mass. -/
theorem values_length (values : List (Value Symbol Guard)) : values.length ≤ InternedValueMass.values values := by
  rw [InternedValueMass.values_eq_length_sum]
  omega

/-- Every original row occurrence contributes to its complete list mass. -/
theorem edges_length (rows : List (EdgeValue Symbol Guard)) : rows.length ≤ InternedValueMass.edges rows := by
  rw [InternedValueMass.edges_eq_length_sum]
  omega

/-- Actual equal-symbol requests retain repetitions and fit the original row product. -/
theorem pairs_length [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) :
    (pairs left right).length ≤ left.length * right.length :=
  SourceCurrentAllocatedFiniteOrdinaryNativeProfile.pairs_length_le left right

/-- Complete original payload mass bounds every emitted row-request occurrence. -/
theorem pairs_mass [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) :
    (pairs left right).length ≤ InternedValueMass.edges left * InternedValueMass.edges right :=
  Nat.le_trans (pairs_length left right) (Nat.mul_le_mul (edges_length left) (edges_length right))

/-- Original node payload mass bounds the entire actual row-request width. -/
theorem node_pairs_mass [DecidableEq Symbol] (left right : Value Symbol Guard) :
    (pairs (nodeEdges left) (nodeEdges right)).length ≤ InternedValueMass.value left * InternedValueMass.value right := by
  have raw := pairs_mass (nodeEdges left) (nodeEdges right)
  have lower (value : Value Symbol Guard) : InternedValueMass.edges (nodeEdges value) ≤ InternedValueMass.value value := by
    cases value <;> simp only [nodeEdges, InternedValueMass.value, InternedValueMass.edges] <;> omega
  exact Nat.le_trans raw (Nat.mul_le_mul (lower left) (lower right))

/-- Each captured row request uses smaller payloads from the original lists. -/
theorem pair_input_mass [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard))
    (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (member : rows ∈ pairs left right) :
    InternedValueMass.edge rows.1 < InternedValueMass.edges left ∧ InternedValueMass.edge rows.2 < InternedValueMass.edges right := by
  have included := (pairs_member left right rows).mp member
  exact ⟨InternedValueMass.edge_mem_lt _ _ included.1, InternedValueMass.edge_mem_lt _ _ included.2.1⟩

private theorem sum_le (requests : List A) (cost : A → Nat) (bound : Nat)
    (small : ∀ request ∈ requests, cost request ≤ bound) :
    (requests.map cost).sum ≤ requests.length * bound := by
  induction requests with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := small first List.mem_cons_self
      have tail := ih (fun request member => small request (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- A monotone recursive charge sums over every actual matched occurrence. -/
theorem rows_request_charges [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard))
    (charge : Nat → Nat) (monotone : ∀ {first last}, first ≤ last → charge first ≤ charge last) :
    ((pairs left right).map fun rows => charge (InternedValueMass.edge rows.1 + InternedValueMass.edge rows.2)).sum ≤
      (left.length * right.length) * charge (InternedValueMass.edges left + InternedValueMass.edges right) := by
  have each := sum_le (pairs left right) (fun rows => charge (InternedValueMass.edge rows.1 + InternedValueMass.edge rows.2))
    (charge (InternedValueMass.edges left + InternedValueMass.edges right)) (by
      intro rows member
      have sizes := pair_input_mass left right rows member
      exact monotone (by omega))
  exact Nat.le_trans each (Nat.mul_le_mul_right _ (pairs_length left right))

/-- Each original union occurrence contributes its recursive charge exactly once. -/
theorem union_request_charges (members : List (Value Symbol Guard)) (other : Value Symbol Guard)
    (charge : Nat → Nat) (monotone : ∀ {first last}, first ≤ last → charge first ≤ charge last) :
    (members.map fun member => charge (InternedValueMass.value member + InternedValueMass.value other)).sum ≤
      members.length * charge (InternedValueMass.values members + InternedValueMass.value other) := by
  apply sum_le
  intro member present
  have small := InternedValueMass.value_mem_lt member members present
  exact monotone (by omega)

/-- A completed actual row walk derives its list mass from the current causal store. -/
theorem rows_trace [DecidableEq Symbol]
    (call : (EdgeValue Symbol Guard × EdgeValue Symbol Guard) → Machine Symbol Guard → Result Symbol Guard (EdgeValue Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (before after : Machine Symbol Guard)
    (values : List (EdgeValue Symbol Guard)) (bound : Nat)
    (trace : WalkTrace call (pairs left right) before values after)
    (stored : Stored bound after.heap) (resident : ∀ row ∈ values, EdgeResident after.heap row) :
    values.length ≤ left.length * right.length ∧
      InternedValueMass.edges values ≤ (left.length * right.length) * (1 + bound) := by
  have width : values.length ≤ left.length * right.length := by rw [trace.length]; exact pairs_length left right
  have small := SourceRecursiveIntersectionWorkMass.edges_le values bound
    (fun row member => InternedValueMassHeap.resident after.heap stored row (resident row member))
  exact ⟨width, Nat.le_trans small (Nat.mul_le_mul_right _ width)⟩

/-- A completed actual union walk derives one bounded value at every original position. -/
theorem union_trace
    (call : Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (members : List (Value Symbol Guard)) (before after : Machine Symbol Guard)
    (values : List (Value Symbol Guard)) (bound : Nat)
    (trace : WalkTrace call members before values after)
    (stored : Stored bound after.heap) (available : ∀ value ∈ values, Available after.heap value) :
    values.length = members.length ∧ InternedValueMass.values values ≤ members.length * (1 + bound) := by
  have small := SourceRecursiveIntersectionWorkMass.values_le values bound
    (fun value member => InternedValueMassHeap.available after.heap stored value (available value member))
  exact ⟨trace.length, by simpa only [trace.length] using small⟩

/-- The exact compiled row suffix constructs its own result after the supplied actual walk. -/
theorem compileRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : SourceRecursiveIntersectionCode.NodeCall Symbol Guard)
    (edges : SourceRecursiveIntersectionCode.EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (before middle : Machine Symbol Guard) (values : List (EdgeValue Symbol Guard)) (bound : Nat)
    (trace : WalkTrace (fun rows => edges ⟨domain, rows.1, rows.2⟩) (pairs left right) before values middle)
    (stored : Stored bound middle.heap) (resident : ∀ row ∈ values, EdgeResident middle.heap row) :
    ∃ value after,
      SourceRecursiveIntersectionCode.interpret nodes edges (SourceRecursiveIntersectionCode.compileRows domain left right) before = .done value after ∧
      after.domains = middle.domains ∧
      Stored (inflate (left.length * right.length) bound) after.heap ∧
      InternedValueMass.value value ≤ inflate (left.length * right.length) bound ∧
      after.heap.nodes.next ≤ middle.heap.nodes.next + 1 ∧ after.heap.edges.next = middle.heap.edges.next := by
  let actual := InternedConstructorTemplates.run (makeNode values) middle.heap
  have raw := SourceRecursiveIntersectionWorkMass.node values middle.heap stored
    (fun row member => InternedValueMassHeap.resident middle.heap stored row (resident row member))
  have width := (rows_trace _ left right before middle values bound trace stored resident).1
  have enough := SourceRecursiveIntersectionWorkMass.inflate_width width bound
  have walked : SourceRecursiveIntersectionCode.interpret nodes edges
      (SourceRecursiveIntersectionCode.walk (fun rows => SourceRecursiveIntersectionCode.requestEdge domain rows.1 rows.2) (pairs left right)) before = .done values middle := by
    rw [SourceRecursiveIntersectionCode.interpret_walk]
    simpa only [SourceRecursiveIntersectionCode.interpret_requestEdge_fun] using (walk_done_iff _ _ _ _ _).mpr trace
  refine ⟨actual.1, {middle with heap := actual.2}, ?_, rfl, raw.1.mono enough, Nat.le_trans raw.2.1 enough, raw.2.2.1, raw.2.2.2⟩
  simp only [SourceRecursiveIntersectionCode.compileRows, SourceRecursiveIntersectionCode.interpret_bind,
    walked, Result.bind, SourceRecursiveIntersectionCode.interpret, SourceRecursiveIntersectionCode.result_bind_pure,
    SourceRecursiveIntersectionKernel.work]

/-- The literal compiled union suffix constructs its own result at the actual returned prefix. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : SourceRecursiveIntersectionCode.NodeCall Symbol Guard)
    (edges : SourceRecursiveIntersectionCode.EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (left : Bool)
    (before middle : Machine Symbol Guard) (values : List (Value Symbol Guard)) (bound : Nat)
    (trace : WalkTrace (fun member => nodes (if left then ⟨domain, member, other⟩ else ⟨domain, other, member⟩)) members before values middle)
    (stored : Stored bound middle.heap) (available : ∀ value ∈ values, Available middle.heap value) :
    ∃ value after,
      SourceRecursiveIntersectionCode.interpret nodes edges
        ((SourceRecursiveIntersectionCode.walk (fun member => if left then SourceRecursiveIntersectionCode.requestNode domain member other
          else SourceRecursiveIntersectionCode.requestNode domain other member) members).bind fun values => .work (makeUnion values) .pure) before = .done value after ∧
      after.domains = middle.domains ∧ Stored (inflate members.length bound) after.heap ∧
      InternedValueMass.value value ≤ inflate members.length bound ∧
      after.heap.nodes.next ≤ middle.heap.nodes.next + 1 ∧ after.heap.edges.next = middle.heap.edges.next := by
  let actual := InternedConstructorTemplates.run (makeUnion values) middle.heap
  have raw := SourceRecursiveIntersectionWorkMass.union values middle.heap stored
    (fun value member => InternedValueMassHeap.available middle.heap stored value (available value member))
  have enough : inflate values.length bound = inflate members.length bound := by rw [trace.length]
  have walked : SourceRecursiveIntersectionCode.interpret nodes edges
      (SourceRecursiveIntersectionCode.walk (fun member => if left then SourceRecursiveIntersectionCode.requestNode domain member other
        else SourceRecursiveIntersectionCode.requestNode domain other member) members) before = .done values middle := by
    rw [SourceRecursiveIntersectionCode.interpret_walk]
    have same : (fun member => SourceRecursiveIntersectionCode.interpret nodes edges
        (if left then SourceRecursiveIntersectionCode.requestNode domain member other
          else SourceRecursiveIntersectionCode.requestNode domain other member)) =
        (fun member => nodes (if left then ⟨domain, member, other⟩ else ⟨domain, other, member⟩)) := by
      funext member
      cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, SourceRecursiveIntersectionCode.interpret_requestNode_fun]
    rw [same]
    exact (walk_done_iff _ _ _ _ _).mpr trace
  refine ⟨actual.1, {middle with heap := actual.2}, ?_, rfl, ?_, ?_, raw.2.2.1, raw.2.2.2⟩
  · simp only [SourceRecursiveIntersectionCode.interpret_bind, walked, Result.bind,
      SourceRecursiveIntersectionCode.interpret, SourceRecursiveIntersectionCode.result_bind_pure,
      SourceRecursiveIntersectionKernel.work]
  · simpa only [enough] using raw.1
  · simpa only [enough] using raw.2.1

/-- The selected left-union node branch uses the same actual prefix and constructor result. -/
theorem compileNode_leftUnion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : SourceRecursiveIntersectionCode.NodeCall Symbol Guard)
    (edges : SourceRecursiveIntersectionCode.EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (entry) (members : List (Value Symbol Guard)) (level free)
    (other : Value Symbol Guard) (before middle : Machine Symbol Guard) (values : List (Value Symbol Guard)) (bound : Nat)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.union entry members level free) other = .leftUnion)
    (trace : WalkTrace (fun member => nodes ⟨domain, member, other⟩) members before values middle)
    (stored : Stored bound middle.heap) (available : ∀ value ∈ values, Available middle.heap value) :
    ∃ value after,
      SourceRecursiveIntersectionCode.interpret nodes edges
        (SourceRecursiveIntersectionCode.compileNode ⟨domain, .union entry members level free, other⟩) before = .done value after ∧
      after.domains = middle.domains ∧ Stored (inflate members.length bound) after.heap ∧
      InternedValueMass.value value ≤ inflate members.length bound ∧
      after.heap.nodes.next ≤ middle.heap.nodes.next + 1 ∧ after.heap.edges.next = middle.heap.edges.next := by
  have actual := union nodes edges domain members other true before middle values bound trace stored available
  simpa only [SourceRecursiveIntersectionCode.compileNode, selected, ite_true] using actual

/-- The selected right-union node branch retains the original request orientation. -/
theorem compileNode_rightUnion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : SourceRecursiveIntersectionCode.NodeCall Symbol Guard)
    (edges : SourceRecursiveIntersectionCode.EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (entry) (members : List (Value Symbol Guard)) (level free)
    (other : Value Symbol Guard) (before middle : Machine Symbol Guard) (values : List (Value Symbol Guard)) (bound : Nat)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.union entry members level free) = .rightUnion)
    (trace : WalkTrace (fun member => nodes ⟨domain, other, member⟩) members before values middle)
    (stored : Stored bound middle.heap) (available : ∀ value ∈ values, Available middle.heap value) :
    ∃ value after,
      SourceRecursiveIntersectionCode.interpret nodes edges
        (SourceRecursiveIntersectionCode.compileNode ⟨domain, other, .union entry members level free⟩) before = .done value after ∧
      after.domains = middle.domains ∧ Stored (inflate members.length bound) after.heap ∧
      InternedValueMass.value value ≤ inflate members.length bound ∧
      after.heap.nodes.next ≤ middle.heap.nodes.next + 1 ∧ after.heap.edges.next = middle.heap.edges.next := by
  have actual := union nodes edges domain members other false before middle values bound trace stored available
  simpa only [SourceRecursiveIntersectionCode.compileNode, selected, Bool.false_eq_true, ite_false] using actual

end MicroCFTA.SourceRecursiveIntersectionCompileMass
