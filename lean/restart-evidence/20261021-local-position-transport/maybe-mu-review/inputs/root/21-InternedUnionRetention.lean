import MicroCFTA.InternedEdgeResidency

/-!
# Retention of recursive operands by source union reconstruction

A recursive operand prevents the all-ordinary edge merge. Canonical
identity deduplication retains that operand, and coherent cache readback
retains its complete record. This supplies a constructor-derived retained
path for the nested-binder separation proof.
-/
namespace MicroCFTA.InternedUnionRetention
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedUnionSeparation
open InternedBinderProtocol (NodeKey NodeRef)

/-- On resident records, source identity deduplication retains each complete
input value. It can remove only another occurrence of the same record. -/
theorem distinctNodes_retains (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (resident : ∀ value ∈ values, Resident state value)
    (value : Value Symbol Guard) (member : value ∈ values) : value ∈ distinctNodes values := by
  obtain ⟨kept, present, same⟩ := distinctNodes_covers values value member
  have equal := resident_reference_injective state coherent kept value
    (resident kept (distinctNodes_member values kept present)) (resident value member) same
  simpa [equal] using present

/-- A stored Mu operand prevents the source all-ordinary branch. -/
theorem ordinaryEdges_mu (values : List (Value Symbol Guard))
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (member : Value.mu entry body depth ordinary ∈ values) : ordinaryEdges values = none := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] <;> try rfl
      case node =>
        have tail : Value.mu entry body depth ordinary ∈ rest := by simpa using member
        simp [ih tail]

/-- A Mu operand survives source union reconstruction as a complete stored
descendant. The proof includes singleton return and canonical cache hits. -/
theorem makeUnion_retains_mu [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (member : Value.mu entry body depth ordinary ∈ values.flatMap unionMembers) :
    Retains (.mu entry body depth ordinary) (run (makeUnion values) state).1 := by
  let needle := Value.mu entry body depth ordinary
  change Retains needle (run (makeUnion values) state).1
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value present
    obtain ⟨source, included, selected⟩ := List.mem_flatMap.mp present
    exact unionMembers_available source (available source included) value selected
  have needleAvailable : Available state needle := allAvailable needle member
  have retained : needle ∈ distinctNodes (values.flatMap unionMembers) :=
    distinctNodes_retains state coherent _ (fun value present => (allAvailable value present).resident) needle member
  have completed := makeUnion_available values state coherent cached available
  have needleLater := available_after_run (makeUnion values) state coherent.valid needleAvailable
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [normalized] at retained
  | cons first rest =>
      cases rest with
      | nil =>
          have same : needle = first := by simpa [normalized] using retained
          simpa only [makeUnion, normalized, run, same] using (Retains.here (needle := first))
      | cons second tail =>
          let members := first :: second :: tail
          have present : needle ∈ members := by simpa [normalized, members] using retained
          have notOrdinary : ordinaryEdges members = none := ordinaryEdges_mu members entry body depth ordinary present
          have noEdges : ordinaryEdges (first :: second :: tail) = none := notOrdinary
          let key := NodeKey.union (members.map Value.referenceOf)
          let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
          let result := (nodeStep key identify state).1
          let after := (nodeStep key identify state).2
          have resultAvailable : Available after result := by
            simpa only [makeUnion, normalized, noEdges, run] using completed.2.2
          have needleAfter : Available after needle := by
            simpa only [makeUnion, normalized, noEdges, run] using needleLater
          have afterCoherent : Coherent after := by
            simpa only [makeUnion, normalized, noEdges, run] using completed.1
          obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
            (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
          change NodeFields key actual result at fields
          have sourceResult : (run (makeUnion values) state).1 = result := by
            simp only [makeUnion, normalized, noEdges, run]
            rfl
          rw [sourceResult]
          cases found : result with
          | empty | reference | node | mu => simp [found, NodeFields, key, muKey] at fields
          | union actual actualMembers actualDepth actualFree =>
              simp only [found, NodeFields] at fields
              have sameIds : members.map Value.referenceOf = actualMembers.map Value.referenceOf :=
                NodeKey.union.inj fields.2.1
              have hasId : needle.referenceOf ∈ actualMembers.map Value.referenceOf := by
                rw [← sameIds]
                exact List.mem_map.mpr ⟨needle, present, rfl⟩
              obtain ⟨selected, selectedMember, equalId⟩ := List.mem_map.mp hasId
              have selectedAvailable := resultAvailable.children selected (by simp [found, children, selectedMember])
              have equal := resident_reference_injective after afterCoherent selected needle
                selectedAvailable.resident needleAfter.resident equalId
              apply Retains.step (child := needle) ?_ .here
              simpa [found, semanticChildren, ← equal] using selectedMember

end MicroCFTA.InternedUnionRetention
