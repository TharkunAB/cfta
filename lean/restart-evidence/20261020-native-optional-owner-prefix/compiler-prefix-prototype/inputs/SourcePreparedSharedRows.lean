import MicroCFTA.MergedPreparedReaderEffects
import MicroCFTA.MergedSourceExposureCoverage
import MicroCFTA.SourcePhysicalSharedRows

/-!
# Finite shared rows from prepared Mu and union records

The actual issued map supplies each canonical payload. Finite source row
reads preserve the fixed prepared cache. Each row retains its symbol,
constraint, and ordered child identities. Open probe records have no rows.
-/
namespace MicroCFTA.SourcePreparedSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency InternedFreshProbeKeys
open MergedPhysicalWarmup MergedPhysicalMergeContext

/-- Recursive and union records retain their actual canonical source identities. -/
def reference : Value Symbol Guard → SourceInternedRows.Ref
  | .node entry .. | .mu entry .. | .union entry .. => some entry.identity
  | _ => none

/-- Empty records use the separate empty state. -/
def encode (value : Value Symbol Guard) : SourceInternedRows.State := SourceInternedRows.stateOf (reference value)

/-- Read the actual payload under an issued structural key. -/
def read (state : State Symbol Guard) (identity : Nat) : Option (Value Symbol Guard) :=
  (state.nodes.issued identity).bind state.nodeRecords

/-- Copy each complete source edge without changing its annotations or child order. -/
def exposure (edge : EdgeValue Symbol Guard) : SourceInternedRows.Row Symbol Guard :=
  ⟨edge.entry.key.symbol, edge.children.map reference, edge.entry.key.constraint⟩

/-- A closed available record has finite exact rows in the same prepared cache. -/
theorem read_finite [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ edges, ∃ fuel, MergedSourceExposure.nodeEdges fuel value state = .done edges state ∧
      Edges state edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, MergedSourceExposure.nodeEdges (fuel + extra) value state = .done edges state := by
  obtain ⟨fuel, edges, after, done, _, _, _, _, _, resident, children, stable⟩ :=
    MergedColdReaderFacts.read_closed value state context.facts prepared available closed
  have same := MergedPreparedReaderEffects.done_state fuel value state outputs context available edges after done
  subst after
  exact ⟨edges, fuel, done, resident, children, stable⟩

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Select the exact stable finite source result; inaccessible open records are omitted. -/
def rows [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) : List (EdgeValue Symbol Guard) :=
  if input : Available state value ∧ value.free = [] then
    Classical.choose (read_finite state outputs context prepared value input.1 input.2)
  else []

/-- The selected list is an actual stable source result with resident closed children. -/
theorem rows_read [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ fuel, MergedSourceExposure.nodeEdges fuel value state = .done (rows state outputs context prepared value) state ∧
      Edges state (rows state outputs context prepared value) ∧
      MergedColdReaderClosedInputs.ClosedEdges (rows state outputs context prepared value) ∧
      ∀ extra, MergedSourceExposure.nodeEdges (fuel + extra) value state = .done (rows state outputs context prepared value) state := by
  have input : Available state value ∧ value.free = [] := ⟨available, closed⟩
  simp only [rows, dite_eq_left input]
  exact Classical.choose_spec (read_finite state outputs context prepared value available closed)

/-- The physical issued map and finite source reads supply the shared heap. -/
def heap [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state) :
    SourceInternedRows.Heap Symbol Guard := fun identity =>
  (read state identity).toList.flatMap fun value => (rows state outputs context prepared value).map exposure

/-- Every payload read from the actual maps is available. -/
theorem read_available (state : State Symbol Guard) (facts : Facts state) (identity : Nat) (value : Value Symbol Guard)
    (found : read state identity = some value) : Available state value := by
  obtain ⟨key, _, stored⟩ := Option.bind_eq_some_iff.mp found
  exact facts.cached.nodes key value stored

/-- Each nonempty available record is read under its exact identity, including Mu and union records. -/
theorem read_identity (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (available : Available state value) (identity : Nat) (same : reference value = some identity) :
    read state identity = some value := by
  cases value <;> simp only [reference] at same <;> try contradiction
  all_goals
    obtain rfl := Option.some.inj same
    have stored := resident_entry state facts.coherent _ available.resident _ rfl
    have issued := (facts.coherent.valid.2.2 _ _ stored).2
    simp only [read, issued, Option.bind_some]
    exact available.resident _ rfl

/-- Source references remain below the actual issued counter. -/
theorem reference_bounded (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (available : Available state value) (identity : Nat) (same : reference value = some identity) :
    identity < state.nodes.next := by
  cases value <;> simp only [reference] at same <;> try contradiction
  all_goals
    obtain rfl := Option.some.inj same
    exact IntersectionFlatMemoKeyPhysical.entry_bounded state facts _ available _ rfl

/-- Every selected row child is available and closed in the same cache. -/
theorem rows_child [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ rows state outputs context prepared value) (child : Value Symbol Guard)
    (inside : child ∈ edge.children) : Available state child ∧ child.free = [] := by
  by_cases input : Available state value ∧ value.free = []
  · obtain ⟨_, _, resident, closed, _⟩ := rows_read state outputs context prepared value input.1 input.2
    exact ⟨context.facts.cached.edges edge.entry.key edge (resident edge member) child inside, closed edge member child inside⟩
  · simp [rows, input] at member

/-- The finite issued counter contains every child reached by the actual shared rows. -/
theorem heap_closed [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state) :
    SourceInternedRows.ClosedDomain (heap state outputs context prepared) (List.range state.nodes.next) := by
  intro identity _ child member
  have pending := (SourceInternedRows.mem_successors (heap state outputs context prepared) identity child).mp member
  obtain ⟨row, present, inside⟩ := List.mem_flatMap.mp pending
  obtain ⟨value, _, present⟩ := List.mem_flatMap.mp present
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp present
  obtain ⟨childValue, childIn, same⟩ := List.mem_map.mp inside
  exact List.mem_range.mpr (reference_bounded state context.facts childValue
    (rows_child state outputs context prepared value edge edgeIn childValue childIn).1 child same)

/-- Every available root has a finite stable shared traversal through Mu and union records. -/
theorem toRows_finite [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) :
    ∃ fuel raw, ∀ larger, fuel ≤ larger →
      SourceInternedRows.toRows (heap state outputs context prepared) larger (reference value) = some raw := by
  apply SourceInternedRows.toRows_finite _ (List.range state.nodes.next) (heap_closed state outputs context prepared)
  intro identity same
  exact List.mem_range.mpr (reference_bounded state context.facts value available identity same)

end
end MicroCFTA.SourcePreparedSharedRows
