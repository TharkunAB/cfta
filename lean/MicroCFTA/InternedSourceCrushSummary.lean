import MicroCFTA.InternedSourceCrushSemantics

/-!
# Exact summaries of actual visited-node execution

Fresh canonical roots add their own local check and source children.
Repeated identities use the complete immutable record from the same cache.
The mutual source induction derives every summary without a fold law.
-/
namespace MicroCFTA.InternedSourceCrush
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open InternedEdgeResidency (nodeEdges)

/-- A checked canonical root removes its own exclusion from the fresh-record property. -/
theorem Added.drop_head (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (entry : Interned NodeKey) (available : Available state value)
    (field : entryOf value = some entry) (seen result : List Nat) (property : Value Symbol Guard → Prop)
    (own : property value) (rest : Added state (entry.identity :: seen) result property) :
    Added state seen result property := by
  intro other actual otherAvailable otherField member fresh
  by_cases same : actual.identity = entry.identity
  · have equal := InternedFreshProbeKeys.resident_identity_unique state coherent other value
      otherAvailable.resident available.resident actual entry otherField field same
    exact equal ▸ own
  · exact rest other actual otherAvailable otherField member (by simpa [same] using fresh)

/-- A fresh source root combines its local check with its complete actual child summary. -/
theorem wrap_summary (plain : Guard → Bool) (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (entry : Interned NodeKey) (available : Available state value)
    (field : entryOf value = some entry) (seen : List Nat) (fresh : entry.identity ∉ seen)
    (result : Bool × List Nat) (body : Summary plain state (sourceChildren value) (entry.identity :: seen) result)
    (growth : (entry.identity :: seen) ⊆ result.2) :
    Summary plain state [value] seen (localPlain plain value && result.1, result.2) := by
  have rootEntered := growth List.mem_cons_self
  have rootClosed : ClosedAt result.2 value := body.entered
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other member actual otherField
    have same : other = value := List.mem_singleton.mp member
    subst other
    have equal := Option.some.inj (field.symm.trans otherField)
    exact equal ▸ rootEntered
  · exact Added.drop_head state coherent value entry available field seen result.2 _ rootClosed body.closed
  · refine Added.drop_head state coherent value entry available field seen result.2 (Reaches [value]) (.root value (by simp)) ?_
    exact body.origins.mono (fun other reached => reached.mono
      (fun child member => .child value child (.root value (by simp)) member))
  · rw [Bool.and_eq_true, body.checked]
    constructor
    · rintro ⟨own, rest⟩
      exact Added.drop_head state coherent value entry available field seen result.2 _ own rest
    · intro checked
      exact ⟨checked value entry available field rootEntered fresh,
        checked.restrict (fun _ member => List.mem_cons_of_mem _ member)⟩

mutual
/-- Every actual source node visit derives exact canonical reachability, closure, and Boolean checks. -/
theorem visit_summary (plain : Guard → Bool) (value : Value Symbol Guard) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    Summary plain state [value] seen (visit plain value seen) := by
  cases value with
  | empty | reference => simpa only [visit] using primitive_summary plain state _ seen rfl
  | node entry edges depth free =>
      rw [visit]
      split
      · rename_i visited; exact seen_summary plain state _ entry rfl seen visited
      · rename_i fresh
        have body := visitEdges_summary plain edges (entry.identity :: seen) state coherent (fun child member => available.children child member)
        simpa only [sourceChildren, localPlain, nodeEdges] using
          wrap_summary plain state coherent _ entry available rfl seen fresh _ body (visitEdges_grows plain edges _)
  | union entry values depth free =>
      rw [visit]
      split
      · rename_i visited; exact seen_summary plain state _ entry rfl seen visited
      · rename_i fresh
        have body := visitMany_summary plain values (entry.identity :: seen) state coherent (fun child member => available.children child member)
        simpa only [sourceChildren, localPlain, nodeEdges, List.all_nil, Bool.true_and] using
          wrap_summary plain state coherent _ entry available rfl seen fresh _ body (visitMany_grows plain values _)
  | mu entry body depth ordinary =>
      rw [visit]
      split
      · rename_i visited; exact seen_summary plain state _ entry rfl seen visited
      · rename_i fresh
        have inside := visit_summary plain body (entry.identity :: seen) state coherent (available.children body (by simp [children]))
        simpa only [sourceChildren, localPlain, nodeEdges, List.all_nil, Bool.true_and] using
          wrap_summary plain state coherent _ entry available rfl seen fresh _ inside (visit_grows plain body _)
termination_by sizeOf value

/-- Ordered child execution composes complete summaries through each actual visited set. -/
theorem visitMany_summary (plain : Guard → Bool) (values : List (Value Symbol Guard)) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state) (available : ∀ value ∈ values, Available state value) :
    Summary plain state values seen (visitMany plain values seen) := by
  cases values with
  | nil => simpa only [visitMany] using nil_summary plain state seen
  | cons first rest =>
      have head := visit_summary plain first seen state coherent (available first List.mem_cons_self)
      have tail := visitMany_summary plain rest (visit plain first seen).2 state coherent (fun value member => available value (List.mem_cons_of_mem first member))
      simpa only [visitMany, List.singleton_append] using sequence_summary plain state [first] rest seen _ _ head tail
        (visit_grows plain first seen) (visitMany_grows plain rest _)
termination_by sizeOf values

/-- Original edge child order has exact canonical summary composition. -/
theorem visitEdges_summary (plain : Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) :
    Summary plain state (edges.flatMap EdgeValue.children) seen (visitEdges plain edges seen) := by
  cases edges with
  | nil => simpa only [visitEdges, List.flatMap_nil] using nil_summary plain state seen
  | cons first rest =>
      cases first with
      | mk entry children =>
          have head := visitMany_summary plain children seen state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
          have tail := visitEdges_summary plain rest (visitMany plain children seen).2 state coherent (fun value member => available value (by simp [member]))
          simpa only [visitEdges, List.flatMap_cons, EdgeValue.children] using
            sequence_summary plain state children (rest.flatMap EdgeValue.children) seen _ _ head tail
              (visitMany_grows plain children seen) (visitEdges_grows plain rest _)
termination_by sizeOf edges
end

end MicroCFTA.InternedSourceCrush
