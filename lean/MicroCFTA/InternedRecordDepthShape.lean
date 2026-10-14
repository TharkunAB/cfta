import MicroCFTA.InternedFreshOrdinaryDepthComposition
import MicroCFTA.InternedRootProfileReflection

/-!
# Complete captured records supply exact depth shapes

The decoder keeps root alternatives even when another alternative is
opaque. Ordinary nodes and Mu records place their free names below a
boundary. A union combines the complete shapes of its original members.
Coherent availability supplies its cached free-name equation.
-/
namespace MicroCFTA.InternedRecordDepthShape
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedDepthSemantics
open InternedDeepFreeDepth
open InternedBinderProtocol (Reference)

mutual
/-- Decode every complete record's root alternatives, deep names, opacity, and actual cached depth. -/
def shape : Value Symbol Guard → Shape Reference
  | .empty => {}
  | .reference name => ⟨[name], [], false, 0⟩
  | value@(.node ..) | value@(.mu ..) => ⟨[], value.free, true, value.depth⟩
  | .union _ members depth _ => {combineMany (shapes members) with depth := depth}
termination_by value => sizeOf value

/-- Decode union members in their original order. -/
def shapes : List (Value Symbol Guard) → List (Shape Reference)
  | [] => []
  | first :: rest => shape first :: shapes rest
termination_by values => sizeOf values
end

/-- The ordered decoder is the map of the complete record decoder. -/
theorem shapes_map (values : List (Value Symbol Guard)) : shapes values = values.map shape := by
  induction values with
  | nil => rw [shapes]; rfl
  | cons first rest ih => rw [shapes, List.map_cons, ih]

/-- Complete shape decoding retains the actual cached depth, including stored union depth. -/
theorem shape_depth (value : Value Symbol Guard) : (shape value).depth = value.depth := by
  cases value <;> simp only [shape, Value.depth]

mutual
/-- Ordered shape combination retains exactly the deep names of the decoded records. -/
theorem shapes_deep (values : List (Value Symbol Guard)) : (combineMany (shapes values)).deep = deepMany values := by
  cases values with
  | nil => rw [shapes, combineMany, deepMany]
  | cons first rest => rw [shapes, combineMany, deepMany]; simp only [combine]; rw [shape_deep first, shapes_deep rest]
termination_by sizeOf values

/-- Complete shape decoding retains every actual deep occurrence. -/
theorem shape_deep (value : Value Symbol Guard) : (shape value).deep = deepNames value := by
  cases value with
  | empty | reference | node | mu => simp only [shape, deepNames]
  | union entry members depth free => simpa only [shape, deepNames] using shapes_deep members
termination_by sizeOf value
end

/-- The pure profile fold agrees with the actual ordered source profile fold. -/
theorem combine_profiles (values : List (Value Symbol Guard)) :
    InternedProfileSemantics.combineMany (values.map InternedRootProfile.profile) = InternedRootProfile.many values := by
  induction values with
  | nil => simp [InternedProfileSemantics.combineMany, InternedRootProfile.many]
  | cons first rest ih =>
      rw [List.map_cons, InternedProfileSemantics.combineMany, ih, InternedRootProfile.many]
      cases InternedRootProfile.profile first <;> cases InternedRootProfile.many rest <;> rfl

mutual
/-- The decoded shape retains the complete actual root profile. -/
theorem shape_profile (value : Value Symbol Guard) :
    InternedDepthSemanticProjections.profile (shape value) = InternedRootProfile.profile value := by
  cases value with
  | empty | reference | node | mu => simp only [shape, InternedDepthSemanticProjections.profile, InternedRootProfile.profile, Bool.false_eq_true, ↓reduceIte]
  | union entry members depth free =>
      rw [shape, InternedRootProfile.profile]
      change InternedDepthSemanticProjections.profile (combineMany (shapes members)) = InternedRootProfile.many members
      rw [InternedDepthSemanticProjections.profile_many, shapes_profile, combine_profiles]
termination_by sizeOf value

/-- Ordered shape decoding retains the exact original profile list. -/
theorem shapes_profile (values : List (Value Symbol Guard)) :
    (shapes values).map InternedDepthSemanticProjections.profile = values.map InternedRootProfile.profile := by
  cases values with
  | nil => rw [shapes]; rfl
  | cons first rest => rw [shapes, List.map_cons, List.map_cons, shape_profile first, shapes_profile rest]
termination_by sizeOf values
end

mutual
/-- Every decoded record has no deep occurrence without an opaque alternative. -/
theorem shape_coherent (value : Value Symbol Guard) : InternedDepthSemanticProjections.Coherent (shape value) := by
  cases value with
  | empty | reference | node | mu => simp [shape, InternedDepthSemanticProjections.Coherent]
  | union entry members depth free =>
      rw [shape]
      change InternedDepthSemanticProjections.Coherent (combineMany (shapes members))
      exact InternedDepthSemanticProjections.coherent_many _ (shapes_coherent members)
termination_by sizeOf value

/-- Every ordered decoded environment satisfies the pure shape representation condition. -/
theorem shapes_coherent (values : List (Value Symbol Guard)) : InternedDepthSemanticProjections.CoherentMany (shapes values) := by
  cases values with
  | nil => rw [shapes]; intro value member; cases member
  | cons first rest =>
      rw [shapes]
      intro value member
      rcases List.mem_cons.mp member with rfl | included
      · exact shape_coherent first
      · exact shapes_coherent rest value included
termination_by sizeOf values
end

mutual
/-- An available coherent record has exactly the decoded free-name membership. -/
theorem shape_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (name : Reference) : name ∈ (shape value).free ↔ name ∈ value.free := by
  cases value with
  | empty | reference | node | mu => simp only [shape, Shape.free, Value.free, List.nil_append, List.append_nil]
  | union entry members depth free =>
      rw [shape]
      change name ∈ (combineMany (shapes members)).free ↔ name ∈ free
      rw [InternedNormalizationFree.union_free state coherent entry members depth free available.resident, childFree_member]
      exact shapes_free members state coherent (fun value member => available.children value member) name
termination_by sizeOf value

/-- Decoded ordered operands retain all and only the original free occurrences. -/
theorem shapes_free (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value) (name : Reference) :
    name ∈ (combineMany (shapes values)).free ↔ ∃ value ∈ values, name ∈ value.free := by
  cases values with
  | nil => simp [shapes, combineMany, Shape.free]
  | cons first rest =>
      rw [shapes, combineMany, InternedDepthFreeProjection.combine_member,
        shape_free first state coherent (available first List.mem_cons_self) name,
        shapes_free rest state coherent (fun value member => available value (List.mem_cons_of_mem first member)) name]
      simp
termination_by sizeOf values
end

/-- Actual normalized available records supply the complete depth observation without a representation premise. -/
theorem observed (value : Value Symbol Guard) (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : Available state value) : InternedFreshOrdinaryDepthComposition.Observed value (shape value) := by
  refine ⟨?_, (shape_depth value).symm, ?_⟩
  · rw [← InternedDepthSemanticProjections.profile_empty, shape_profile]
    exact (InternedRootProfileNode.isEmpty_profile value state normal.proper available).symm
  · intro name
    rw [shape_deep]

/-- Every decoded lexical input satisfies the pure shape condition. -/
theorem input_coherent (values : List (Value Symbol Guard)) :
    InternedDepthSemanticProjections.CoherentMany (values.map shape) := by
  rw [← shapes_map]
  exact shapes_coherent values

/-- Decoding the lexical inputs retains their exact original root profiles. -/
theorem input_profiles (values : List (Value Symbol Guard)) :
    (values.map shape).map InternedDepthSemanticProjections.profile = values.map InternedRootProfile.profile := by
  rw [← shapes_map]
  exact shapes_profile values

/-- Every optional lexical lookup retains the complete actual free-name membership. -/
theorem input_free (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value) (index : Nat) (name : Reference) :
    name ∈ (((values.map shape).map Shape.free)[index]?).getD [] ↔ name ∈ ((values.map Value.free)[index]?).getD [] := by
  cases found : values[index]? with
  | none => simp [List.getElem?_map, found]
  | some value =>
      simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using
        shape_free value state coherent (available value (List.mem_of_getElem? found)) name

end MicroCFTA.InternedRecordDepthShape
