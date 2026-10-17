import MicroCFTA.InternedValueMass
import MicroCFTA.SourceRecursiveIntersectionSourceProfile

/-!
# Causal mass bounds for complete stored payloads

One positive bound covers both actual record maps. Pending keys need no
payload. Initial bounds use successful reads in the actual issued ranges.
An insertion keeps the earlier winner or installs its bounded candidate.
-/
namespace MicroCFTA.InternedValueMassHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency
namespace M := InternedValueMass
namespace P := SourceRecursiveIntersectionSourceProfile
variable {Symbol Guard : Type} {bound larger : Nat}

/-- Both complete record maps retain a positive common payload bound. -/
structure Stored (bound : Nat) (state : State Symbol Guard) : Prop where
  /-- Empty and reference values also fit the bound. -/
  positive : 1 ≤ bound
  /-- Every completed node payload fits the bound at its actual key. -/
  nodes : ∀ key value, state.nodeRecords key = some value → M.value value ≤ bound
  /-- Every completed edge payload fits the same bound. -/
  edges : ∀ key edge, state.edgeRecords key = some edge → M.edge edge ≤ bound

/-- Increasing the common bound retains both causal payload laws. -/
theorem Stored.mono {state : State Symbol Guard} (stored : Stored bound state)
    (increase : bound ≤ larger) : Stored larger state :=
  ⟨Nat.le_trans stored.positive increase,
    fun key value found => Nat.le_trans (stored.nodes key value found) increase,
    fun key edge found => Nat.le_trans (stored.edges key edge found) increase⟩

/-- Empty record maps satisfy every positive common bound. -/
theorem empty_stored (positive : 1 ≤ bound) : Stored bound (empty : State Symbol Guard) :=
  ⟨positive, by intro key value absent; cases absent, by intro key edge absent; cases absent⟩

/-- Sum actual payload masses in both independent issued ranges. -/
def initialBound (source : State Symbol Guard) : Nat :=
  1 + ((P.nodePayloads source).map M.value).sum + ((P.edgePayloads source).map M.edge).sum

private theorem member_sum {Item : Type} (measure : Item → Nat) (items : List Item)
    (item : Item) (member : item ∈ items) : measure item ≤ (items.map measure).sum := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp only [List.map_cons, List.sum_cons]; omega
    · have lower := ih later
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Coherent initial records establish the computed store bound without a future execution. -/
theorem initial (source : State Symbol Guard) (facts : Facts source) : Stored (initialBound source) source := by
  refine ⟨by simp only [initialBound]; omega, ?_, ?_⟩
  · intro key value found
    obtain ⟨entry, present, _fields⟩ := facts.coherent.nodes key value found
    have issued := (facts.coherent.valid.2.2 key entry present).2
    have captured : SourcePreparedSharedRows.read source entry.identity = some value := by
      simp only [SourcePreparedSharedRows.read, issued, Option.bind_some]
      exact found
    have lower := member_sum M.value _ _ (P.node_mem source facts entry.identity value captured)
    simp only [initialBound]
    omega
  · intro key edge found
    have captured := P.resident_read source facts edge found
    have lower := member_sum M.edge _ _ (P.edge_mem source facts edge.entry.identity edge captured)
    simp only [initialBound]
    omega

/-- Availability supplies a stored payload or a unit-mass Empty or reference. -/
theorem available (source : State Symbol Guard) (stored : Stored bound source)
    (value : Value Symbol Guard) (known : Available source value) : M.value value ≤ bound := by
  cases value with
  | empty | reference => exact stored.positive
  | node entry rows depth free | mu entry rows depth free | union entry rows depth free =>
    exact stored.nodes entry.key _ (known.resident entry rfl)

/-- Exact edge residency supplies the stored edge mass bound. -/
theorem resident (source : State Symbol Guard) (stored : Stored bound source)
    (edge : EdgeValue Symbol Guard) (known : EdgeResident source edge) : M.edge edge ≤ bound :=
  stored.edges edge.entry.key edge known

/-- Cache reservation changes no complete payload map. -/
theorem Stored.node_cache {state : State Symbol Guard} (stored : Stored bound state)
    (cache : Cache.State InternedBinderProtocol.NodeKey) : Stored bound {state with nodes := cache} :=
  ⟨stored.positive, stored.nodes, stored.edges⟩

/-- Changing the edge identity cache changes no complete payload map. -/
theorem Stored.edge_cache {state : State Symbol Guard} (stored : Stored bound state)
    (cache : Cache.State (EdgeKey Symbol Guard)) : Stored bound {state with edges := cache} :=
  ⟨stored.positive, stored.nodes, stored.edges⟩

/-- A node insertion bounds its own candidate and retains every earlier winner. -/
theorem Stored.put_node {state : State Symbol Guard} (stored : Stored bound state)
    (key : InternedBinderProtocol.NodeKey) (candidate : Value Symbol Guard) (bounded : M.value candidate ≤ bound) :
    Stored bound {state with nodeRecords := keepFirst state.nodeRecords key candidate} := by
  refine ⟨stored.positive, ?_, stored.edges⟩
  intro other value found
  rcases record_cases state.nodeRecords key other candidate value found with old | ⟨rfl, rfl⟩
  · exact stored.nodes other value old
  · exact bounded

/-- An edge insertion bounds its own candidate and retains every earlier winner. -/
theorem Stored.put_edge [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard}
    (stored : Stored bound state) (key : EdgeKey Symbol Guard) (candidate : EdgeValue Symbol Guard)
    (bounded : M.edge candidate ≤ bound) :
    Stored bound {state with edgeRecords := keepFirst state.edgeRecords key candidate} := by
  refine ⟨stored.positive, stored.nodes, ?_⟩
  intro other edge found
  rcases record_cases state.edgeRecords key other candidate edge found with old | ⟨rfl, rfl⟩
  · exact stored.edges other edge old
  · exact bounded

/-- One actual node step bounds the candidate before it reads the current winner. -/
theorem node_step (key : InternedBinderProtocol.NodeKey)
    (identify : Interned InternedBinderProtocol.NodeKey → Value Symbol Guard) (state : State Symbol Guard)
    (stored : Stored bound state) (candidateBound : Nat)
    (candidate : ∀ entry, M.value (identify entry) ≤ candidateBound) :
    Stored (max bound candidateBound) (nodeStep key identify state).2 ∧
      M.value (nodeStep key identify state).1 ≤ max bound candidateBound := by
  let selected := (Cache.intern state.nodes key).1
  have after := ((stored.mono (Nat.le_max_left bound candidateBound)).node_cache
    (Cache.intern state.nodes key).2).put_node key (identify selected)
    (Nat.le_trans (candidate selected) (Nat.le_max_right bound candidateBound))
  refine ⟨after, ?_⟩
  obtain ⟨winner, present⟩ := keepFirst_present state.nodeRecords key (identify selected)
  have bounded := after.nodes key winner present
  simpa only [nodeStep, selected, present, Option.getD_some] using bounded

/-- One actual edge step bounds the candidate before it reads the current winner. -/
theorem edge_step [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (state : State Symbol Guard)
    (stored : Stored bound state) (candidateBound : Nat)
    (candidate : ∀ entry, M.edge (identify entry) ≤ candidateBound) :
    Stored (max bound candidateBound) (edgeStep key identify state).2 ∧
      M.edge (edgeStep key identify state).1 ≤ max bound candidateBound := by
  let selected := (Cache.intern state.edges key).1
  have after := ((stored.mono (Nat.le_max_left bound candidateBound)).edge_cache
    (Cache.intern state.edges key).2).put_edge key (identify selected)
    (Nat.le_trans (candidate selected) (Nat.le_max_right bound candidateBound))
  refine ⟨after, ?_⟩
  obtain ⟨winner, present⟩ := keepFirst_present state.edgeRecords key (identify selected)
  have bounded := after.edges key winner present
  simpa only [edgeStep, selected, present, Option.getD_some] using bounded

end MicroCFTA.InternedValueMassHeap
