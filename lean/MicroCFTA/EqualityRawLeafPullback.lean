import MicroCFTA.EqualityRawLeafUnion
import MicroCFTA.EqualityLeafProjectionCachePullback

/-!
# Raw leaf reconstruction in the actual runtime cache

Every row in the finite carrier passes source admission. Each requested
edge therefore occurs in the returned leaf. Residency of that complete
leaf forces every edge request and the parent request to be cache hits.
Temporary proof-cache entries are not needed by the next runtime pass.
-/
namespace MicroCFTA.EqualityRawLeafPullback
open Cache InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityLeafProjectionWorkers (sequence)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A resident accepted row forces the exact source request to be a cache hit. -/
theorem request_hit (row : Fin symbols × SourceGuards.Guard FullSyntax.Formula)
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state)
    (edge : EdgeValue (Fin symbols) ConstraintKey) (resident : EdgeResident state edge)
    (key : edge.entry.key = EqualityRawLeafConstruction.key row)
    (admitted : EqualityRawLeafConstruction.accepted row.2 = true) :
    run (EqualityRawLeafConstruction.request row) state = (edge, state) := by
  have stored : state.edgeRecords (EqualityRawLeafConstruction.key row) = some edge := by
    simpa only [EdgeResident, key] using resident
  have present := (coherent.edges _ _ stored).1
  simp only [EqualityRawLeafConstruction.key] at stored present
  simp only [EqualityRawLeafConstruction.request, admitted, ↓reduceIte,
    makeEdge, run, List.map_nil]
  simp only [edgeStep, Cache.intern, present, keepFirst, stored, Option.getD_some]

/-- Closed component requests give a closed sequence in the original order. -/
theorem sequence_closed [DecidableEq (EdgeKey Symbol Guard)]
    (requests : List (Work Symbol Guard Result)) (state : State Symbol Guard)
    (values : Work Symbol Guard Result → Result)
    (closed : ∀ request ∈ requests, run request state = (values request, state)) :
    run (sequence requests) state = (requests.map values, state) := by
  induction requests with
  | nil => rfl
  | cons first rest ih =>
      simp only [sequence, run_bind, closed first (by simp),
        ih (fun request member => closed request (by simp [member])), run, List.map_cons]

/-- A finite raw leaf representation replays in any valid cache retaining its actual output. -/
theorem represented_pullback (leaf : Leaf initial symbols)
    (before after : State (Fin symbols) ConstraintKey)
    (beforeFacts : Facts before) (afterFacts : Facts after)
    (value : Value (Fin symbols) ConstraintKey) (resident : Resident before value)
    (represented : Represents build (.leaf leaf) after value) :
    Represents build (.leaf leaf) before value := by
  let declarations := EqualityRawLeafConstruction.declarations (EqualityRawLeafInventory.rawChoices leaf)
  let requests := EqualityRawLeafConstruction.requests declarations
  have afterResident := (EqualityRawLeafUnion.represented_fields leaf value after afterFacts represented).1
  have rowsClosed : ∀ request ∈ requests,
      run request before = ((run request after).1, before) := by
    intro request member
    obtain ⟨declaration, declared, rfl⟩ := List.mem_map.mp member
    obtain ⟨⟨symbol, raw⟩, rawMember, rfl⟩ := List.mem_map.mp declared
    obtain ⟨⟨actual, row⟩, choiceMember, equal⟩ := List.mem_map.mp rawMember
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have selected := (EqualityRawLeafInventory.choices_member leaf actual row).mp choiceMember
    obtain ⟨edge, member, key⟩ :=
      (EqualityRawLeafUnion.represented_keys leaf value after afterFacts represented
        (EqualityRawLeafConstruction.key (actual, row.val.val))).mpr ⟨actual, row, selected, rfl⟩
    have first := request_hit (actual, row.val.val) before beforeFacts.coherent edge
      (resident_edges before beforeFacts.linked value resident edge member) key row.property.2
    have second := request_hit (actual, row.val.val) after afterFacts.coherent edge
      (resident_edges after afterFacts.linked value afterResident edge member) key row.property.2
    rw [second]
    exact first
  have exactAfter : run ((sequence requests).bind makeNode) after = (value, after) := represented
  obtain ⟨rows, sequenceAfter, parentAfter⟩ := bind_closed _ _ after afterFacts.coherent.valid value exactAfter
  have completed := EqualityLeafProjectionWorkers.sequence_completed requests after afterFacts.coherent.valid
  rw [sequenceAfter] at completed
  have sequenceBefore := sequence_closed requests before (fun request => (run request after).1) rowsClosed
  rw [← completed.1] at sequenceBefore
  have parentBefore := EqualityLeafProjectionCachePullback.makeNode_pullback rows before after
    beforeFacts.coherent afterFacts.coherent value resident parentAfter
  change run ((sequence requests).bind makeNode) before = (value, before)
  rw [run_bind, sequenceBefore]
  exact parentBefore

end MicroCFTA.EqualityRawLeafPullback
