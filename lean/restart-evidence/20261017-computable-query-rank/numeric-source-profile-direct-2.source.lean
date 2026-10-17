import MicroCFTA.SourceRecursiveIntersectionInstructionProfile
import MicroCFTA.InternedValueMassHeap

/-!
# Numeric bounds for the initial source payload sums

Successful reads expose their actual record lookups. Each payload fits the
stored mass bound. Each issued-range position contributes at most once.
No distinct-payload or identity-injectivity assumption is required.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNumericSourceProfile
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionSourceProfile
variable {Symbol Guard : Type} {mass : Nat}

private theorem sum_bound {Item : Type} (measure : Item → Nat) (items : List Item)
    (bound : Nat) (known : ∀ item ∈ items, measure item ≤ bound) :
    (items.map measure).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      have head := known first (List.mem_cons_self)
      have tail := ih (fun item member => known item (List.mem_cons_of_mem first member))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

private theorem rows_mass (value : Value Symbol Guard) :
    (nodeEdges value).length ≤ InternedValueMass.value value := by
  cases value with
  | empty | reference | mu | union => simp only [nodeEdges, List.length_nil]; omega
  | node entry rows depth free =>
      have counted := InternedValueMass.edges_eq_length_sum rows
      simp only [nodeEdges, InternedValueMass.value]
      omega

private theorem members_mass (value : Value Symbol Guard) :
    memberCount value ≤ InternedValueMass.value value := by
  cases value with
  | empty | reference | mu | node => simp only [memberCount]; omega
  | union entry members depth free =>
      have counted := InternedValueMass.values_eq_length_sum members
      simp only [memberCount, InternedValueMass.value]
      omega

private theorem arity_mass (edge : EdgeValue Symbol Guard) :
    edge.children.length ≤ InternedValueMass.edge edge := by
  have counted := InternedValueMass.values_eq_length_sum edge.children
  rw [InternedValueMass.edge_children]
  omega

private theorem node_mass (source : State Symbol Guard) (stored : InternedValueMassHeap.Stored mass source)
    (value : Value Symbol Guard) (member : value ∈ nodePayloads source) :
    InternedValueMass.value value ≤ mass := by
  obtain ⟨identity, _inside, found⟩ := List.mem_filterMap.mp member
  obtain ⟨key, _issued, record⟩ := Option.bind_eq_some_iff.mp found
  exact stored.nodes key value record

private theorem edge_mass (source : State Symbol Guard) (stored : InternedValueMassHeap.Stored mass source)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edgePayloads source) :
    InternedValueMass.edge edge ≤ mass := by
  obtain ⟨identity, _inside, found⟩ := List.mem_filterMap.mp member
  obtain ⟨key, _issued, record⟩ := Option.bind_eq_some_iff.mp found
  exact stored.edges key edge record

private theorem node_length (source : State Symbol Guard) :
    (nodePayloads source).length ≤ source.nodes.next := by
  simpa only [nodePayloads, List.length_range] using
    List.length_filterMap_le (SourcePreparedSharedRows.read source) (List.range source.nodes.next)

private theorem edge_length (source : State Symbol Guard) :
    (edgePayloads source).length ≤ source.edges.next := by
  simpa only [edgePayloads, List.length_range] using
    List.length_filterMap_le (edgeRead source) (List.range source.edges.next)

/-- Initial record counters and stored mass bound all three source branching sums. -/
theorem limits_bound (source : State Symbol Guard) (stored : InternedValueMassHeap.Stored mass source) :
    (limits source).rows ≤ source.nodes.next * mass ∧
    (limits source).members ≤ source.nodes.next * mass ∧
    (limits source).arity ≤ source.edges.next * mass := by
  have rows := sum_bound (fun value => (nodeEdges value).length) (nodePayloads source) mass
    (fun value member => Nat.le_trans (rows_mass value) (node_mass source stored value member))
  have members := sum_bound memberCount (nodePayloads source) mass
    (fun value member => Nat.le_trans (members_mass value) (node_mass source stored value member))
  have arity := sum_bound (fun edge => edge.children.length) (edgePayloads source) mass
    (fun edge member => Nat.le_trans (arity_mass edge) (edge_mass source stored edge member))
  exact ⟨Nat.le_trans rows (Nat.mul_le_mul_right mass (node_length source)),
    Nat.le_trans members (Nat.mul_le_mul_right mass (node_length source)),
    Nat.le_trans arity (Nat.mul_le_mul_right mass (edge_length source))⟩

/-- Recomputed initial mass includes every successful issued-range payload occurrence. -/
theorem initial_bound (source : State Symbol Guard) (stored : InternedValueMassHeap.Stored mass source) :
    InternedValueMassHeap.initialBound source ≤ 1 + (source.nodes.next + source.edges.next) * mass := by
  have nodes := Nat.le_trans (sum_bound InternedValueMass.value (nodePayloads source) mass
    (node_mass source stored)) (Nat.mul_le_mul_right mass (node_length source))
  have edges := Nat.le_trans (sum_bound InternedValueMass.edge (edgePayloads source) mass
    (edge_mass source stored)) (Nat.mul_le_mul_right mass (edge_length source))
  simp only [InternedValueMassHeap.initialBound, Nat.add_mul]
  omega

/-- Initial node and edge counters give a numeric request-list branching limit. -/
def branching (nodes edges mass : Nat) : Nat :=
  max 1 (max ((nodes * mass) ^ 2) (max (nodes * mass) (edges * mass)))

/-- The actual source branching limit fits the initial numeric envelope. -/
theorem source_branching (source : State Symbol Guard) (stored : InternedValueMassHeap.Stored mass source) :
    SourceRecursiveIntersectionInstructionProfile.sourceBranching source ≤
      branching source.nodes.next source.edges.next mass := by
  obtain ⟨rows, members, arity⟩ := limits_bound source stored
  have pairs := Nat.mul_le_mul rows rows
  simp only [SourceRecursiveIntersectionInstructionProfile.sourceBranching,
    SourceRecursiveIntersectionInstructionProfile.branching, branching, Nat.pow_two]
  omega

/-- Increasing any initial numeric parameter retains the branching envelope. -/
theorem branching_mono {firstNodes lastNodes firstEdges lastEdges firstMass lastMass : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) (mass : firstMass ≤ lastMass) :
    branching firstNodes firstEdges firstMass ≤ branching lastNodes lastEdges lastMass := by
  have nodeBound := Nat.mul_le_mul nodes mass
  have edgeBound := Nat.mul_le_mul edges mass
  have pairs := Nat.mul_le_mul nodeBound nodeBound
  simp only [branching, Nat.pow_two]
  omega

end MicroCFTA.SourceRecursiveIntersectionNumericSourceProfile
