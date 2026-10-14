import MicroCFTA.InternedFreeNameIndexedOrigins
import MicroCFTA.InternedStoredSubstitutionScope

/-!
# Free-name support of actual stored lexical plans

A used captured slot supplies a free name of the original stored value.
That name is absent from every enclosing local binder. Canonical slot
lookup retains the complete source record, including closed captures.
-/
namespace MicroCFTA.InternedStoredPlanFreeSupport
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedFreeNameIndexedOrigins
open InternedBinderProtocol (Reference)

mutual
/-- Every used captured slot supplies an original free name outside the local binder list. -/
theorem encode_free (context : List (Value Symbol Guard)) (locals : List Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : ∀ item ∈ context, Available state item)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (index : Nat) (leaf : Value Symbol Guard) (found : context[index]? = some leaf)
    (name : Reference) (named : name ∈ leaf.free) (used : Uses (encode context locals value) (locals.length + index)) :
    name ∈ value.free ∧ name ∉ locals := by
  rw [encode.eq_def] at used
  split at used
  · rename_i closed
    rw [Uses] at used
    have slotEqual : slot context value = index := Nat.add_left_cancel used
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp only [closed, ↓reduceIte, List.mem_singleton])
    have selected := slot_lookup context value state coherent inputs member
    rw [slotEqual, found] at selected
    cases selected
    simp only [List.isEmpty_iff.mp closed, List.not_mem_nil] at named
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases value with
    | empty => rw [Uses] at used; cases used
    | reference reference =>
        cases localSlot : locals.findIdx? (· == reference) with
        | some localIndex =>
            simp only [localSlot, Uses] at used
            have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp localSlot).1
            omega
        | none =>
            simp only [localSlot, Uses] at used
            have slotEqual : slot context (.reference reference) = index := Nat.add_left_cancel used
            have selected := slot_lookup context (.reference reference) state coherent inputs (covered _ (by simp))
            rw [slotEqual, found] at selected
            cases selected
            simp only [Value.free, List.mem_singleton] at named
            subst name
            exact ⟨by simp [Value.free], by
              intro member
              have absent := List.findIdx?_eq_none_iff.mp localSlot reference member
              simp at absent⟩
    | node entry edges depth free =>
        have children := encodeEdges_free context locals edges state coherent inputs
          (fun child member => available.children child member) covered index leaf found name named (by simpa only [Uses] using used)
        obtain ⟨child, member, captured, outside⟩ := children
        refine ⟨?_, outside⟩
        rw [Value.free, InternedNormalizationFree.node_free state coherent entry edges depth free available.resident, childFree_member]
        exact ⟨child, member, captured⟩
    | union entry members depth free =>
        obtain ⟨child, member, captured, outside⟩ := encodeMany_free context locals members state coherent inputs
          (fun child member => available.children child member) covered index leaf found name named (by simpa only [Uses] using used)
        refine ⟨?_, outside⟩
        rw [Value.free, InternedNormalizationFree.union_free state coherent entry members depth free available.resident, childFree_member]
        exact ⟨child, member, captured⟩
    | mu entry body depth ordinary =>
        have nested := encode_free context (.interned entry.identity :: locals) body state coherent inputs
          (available.children body (by simp [children])) covered index leaf found name named
          (by simpa only [Uses, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using used)
        refine ⟨?_, fun member => nested.2 (List.mem_cons_of_mem _ member)⟩
        simp only [Value.free, List.mem_filter, bne_iff_ne]
        exact ⟨nested.1, fun equal => nested.2 (by simp [equal])⟩
termination_by sizeOf value

/-- A used ordered operand slot supplies a free name of an actual original child. -/
theorem encodeMany_free (context : List (Value Symbol Guard)) (locals : List Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : ∀ item ∈ context, Available state item)
    (available : ∀ value ∈ values, Available state value) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (index : Nat) (leaf : Value Symbol Guard) (found : context[index]? = some leaf)
    (name : Reference) (named : name ∈ leaf.free) (used : UsesMany (encodeMany context locals values) (locals.length + index)) :
    ∃ value ∈ values, name ∈ value.free ∧ name ∉ locals := by
  cases values with
  | nil => rw [encodeMany, UsesMany] at used; cases used
  | cons first rest =>
      rw [encodeMany, UsesMany] at used
      rcases used with head | tail
      · exact ⟨first, List.mem_cons_self, encode_free context locals first state coherent inputs (available first List.mem_cons_self)
          (fun leaf member => covered leaf (by simp only [manyLeaves, List.mem_append]; exact Or.inl member)) index leaf found name named head⟩
      · obtain ⟨value, member, captured⟩ := encodeMany_free context locals rest state coherent inputs
          (fun value member => available value (List.mem_cons_of_mem first member))
          (fun leaf member => covered leaf (by simp only [manyLeaves, List.mem_append]; exact Or.inr member)) index leaf found name named tail
        exact ⟨value, List.mem_cons_of_mem first member, captured⟩
termination_by sizeOf values

/-- A used edge child slot supplies a free name of an actual original edge child. -/
theorem encodeEdges_free (context : List (Value Symbol Guard)) (locals : List Reference) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : ∀ item ∈ context, Available state item)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (index : Nat) (leaf : Value Symbol Guard) (found : context[index]? = some leaf)
    (name : Reference) (named : name ∈ leaf.free) (used : UsesEdges (encodeEdges context locals edges) (locals.length + index)) :
    ∃ value ∈ edges.flatMap EdgeValue.children, name ∈ value.free ∧ name ∉ locals := by
  cases edges with
  | nil => rw [encodeEdges, UsesEdges] at used; cases used
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [encodeEdges, UsesEdges] at used
          rcases used with head | tail
          · obtain ⟨value, member, captured⟩ := encodeMany_free context locals values state coherent inputs
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp only [edgeLeaves, List.mem_append]; exact Or.inl member)) index leaf found name named head
            exact ⟨value, by simp [EdgeValue.children, member], captured⟩
          · obtain ⟨value, member, captured⟩ := encodeEdges_free context locals rest state coherent inputs
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp only [edgeLeaves, List.mem_append]; exact Or.inr member)) index leaf found name named tail
            exact ⟨value, by simp [EdgeValue.children, member], captured⟩
termination_by sizeOf edges
end

end MicroCFTA.InternedStoredPlanFreeSupport
