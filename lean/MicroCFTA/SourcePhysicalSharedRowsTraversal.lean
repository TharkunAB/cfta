import MicroCFTA.SourcePhysicalSharedRowsMinimum

/-!
# Physical value worklist refines shared-row traversal

The source worklist holds complete node values. It reads each node's own
stored edges and queues their actual child values. This worker is proved
equal to the shared identity-and-heap worker on available plain inputs.
-/
namespace MicroCFTA.SourcePhysicalSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency SourceInternedIntersectionRows

/-- The actual value worklist stores rows directly from the current physical payload. -/
def collectValues : Nat → Cache.Table Nat (List (SourceInternedRows.Row Symbol Unit)) →
    List (Value Symbol Unit) → Option (Cache.Table Nat (List (SourceInternedRows.Row Symbol Unit)))
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, value :: rest =>
      match reference value with
      | none => collectValues fuel seen rest
      | some identity => match seen identity with
        | some _ => collectValues fuel seen rest
        | none => collectValues fuel (Cache.put seen identity ((nodeEdges value).map exposure))
            ((nodeEdges value).flatMap EdgeValue.children ++ rest)

/-- Worklist values retain their complete physical provenance and plain restriction. -/
def Pending (state : State Symbol Unit) (values : List (Value Symbol Unit)) : Prop :=
  ∀ value ∈ values, Available state value ∧ Plain value

/-- Physical and shared readers queue precisely the same ordered child references. -/
theorem children_node (state : State Symbol Unit) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Unit))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry edges depth free)) :
    SourceInternedRows.children (heap state) entry.identity = (edges.flatMap EdgeValue.children).map reference := by
  simp only [SourceInternedRows.children, heap_node state facts entry edges depth free available,
    List.flatMap_map, exposure, List.map_flatMap]

/-- Prepending actual children preserves the worklist's derived provenance. -/
theorem pending_children (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (rest : List (Value Symbol Unit)) (pending : Pending state rest) :
    Pending state ((nodeEdges value).flatMap EdgeValue.children ++ rest) := by
  intro child member
  rcases List.mem_append.mp member with inside | later
  · obtain ⟨edge, selected, childIn⟩ := List.mem_flatMap.mp inside
    exact ⟨child_available state facts value available edge selected child childIn,
      plain.children value edge selected child childIn⟩
  · exact pending child later

/-- Complete physical worklist execution equals the actual shared map worker. -/
theorem collect_readback (state : State Symbol Unit) (facts : Facts state) (fuel : Nat)
    (seen : Cache.Table Nat (List (SourceInternedRows.Row Symbol Unit))) (values : List (Value Symbol Unit))
    (pending : Pending state values) :
    collectValues fuel seen values = SourceInternedRows.collectMap (heap state) fuel seen (values.map reference) := by
  induction fuel generalizing seen values with
  | zero => rfl
  | succ fuel ih =>
      cases values with
      | nil => rfl
      | cons value rest =>
          have own := pending value List.mem_cons_self
          have later : Pending state rest := fun child member => pending child (List.mem_cons_of_mem _ member)
          cases plain : own.2 with
          | empty =>
              simpa only [collectValues, reference, List.map_cons, SourceInternedRows.collectMap] using ih seen rest later
          | node entry edges depth free children =>
              cases found : seen entry.identity with
              | some stored =>
                  simpa only [collectValues, reference, List.map_cons, SourceInternedRows.collectMap, found] using ih seen rest later
              | none =>
                  simp only [collectValues, reference, nodeEdges, List.map_cons, SourceInternedRows.collectMap, found,
                    heap_node state facts entry edges depth free own.1, children_node state facts entry edges depth free own.1]
                  rw [← List.map_append]
                  exact ih _ _ (pending_children state facts _ own.1 own.2 rest later)

/-- The source physical worklist has a finite stable completed map derived from the actual issued counter. -/
theorem collect_finite (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) :
    ∃ fuel visited, ∀ larger, fuel ≤ larger →
      collectValues larger (fun _ => none) [value] = some (SourceInternedRows.stored (heap state) visited) := by
  have supported : SourceInternedRows.PendingDomain (List.range state.nodes.next) [reference value] := by
    intro identity member
    have same : reference value = some identity := (List.mem_singleton.mp member).symm
    exact List.mem_range.mpr (reference_bounded state facts value available identity same)
  obtain ⟨fuel, visited, done⟩ := SourceInternedRows.collect_finite (heap state) (List.range state.nodes.next)
    (heap_closed state facts) [] [reference value] supported
  refine ⟨fuel, visited, ?_⟩
  intro larger enough
  rw [collect_readback state facts larger _ [value] (by intro child member; rw [List.mem_singleton.mp member]; exact ⟨available, plain⟩)]
  change SourceInternedRows.collectMap (heap state) larger (SourceInternedRows.stored (heap state) []) [reference value] = _
  rw [SourceInternedRows.collectMap_exact, SourceInternedRows.collect_stable (heap state) fuel [] [reference value] visited done larger enough]
  rfl

end MicroCFTA.SourcePhysicalSharedRows
