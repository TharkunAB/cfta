import MicroCFTA.InternedBoundaryFilter
import MicroCFTA.InternedUnionNormalForm
import MicroCFTA.InternedFlatProbeCosts

/-!
# Actual source union construction followed by self filtering

The source first constructs the normalized union. Its self filter deletes
an operand exactly when that union has at least two distinct operands and
contains the selected reference. Singleton self remains a bare reference.
The fused equation retains every effect of the first constructor call.
-/
namespace MicroCFTA.InternedUnionFilterFusion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNormalizationFree InternedUnionNormalForm InternedUnionRetention InternedUnionDescendants
open InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol (Reference NodeKey)

/-- Every normalized operand is an actual available record. -/
theorem selected_available (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (available : Values state values) :
    Values state (distinctNodes (values.flatMap unionMembers)) := by
  intro value member
  obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
  exact unionMembers_available source (available source included) value inner

/-- Actual normalized operands contain no root union when source inputs are flat. -/
theorem selected_atomic (values : List (Value Symbol Guard)) (state : State Symbol Guard) (flat : Flat state)
    (available : Values state values) :
    ∀ value ∈ distinctNodes (values.flatMap unionMembers), Atomic value := by
  intro value member
  obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
  exact flat_members source (resident_flat state flat source (available source included).resident) value inner

/-- A literal reference operand prevents the all-ordinary union merge branch. -/
theorem ordinary_none (name : Reference) (values : List (Value Symbol Guard)) (member : .reference name ∈ values) :
    ordinaryEdges values = none := by
  cases found : ordinaryEdges values with
  | none => rfl
  | some edges =>
      obtain ⟨entry, own, depth, free, impossible, _⟩ := ordinaryEdges_contains values edges found (.reference name) member
      cases impossible

/-- The stored-union branch returns precisely its requested complete members and metadata. -/
theorem union_readback [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (first second : Value Symbol Guard) (tail : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values)
    (selected : distinctNodes (values.flatMap unionMembers) = first :: second :: tail)
    (ordinary : ordinaryEdges (first :: second :: tail) = none) :
    ∃ entry, (run (makeUnion values) state).1 = .union entry (first :: second :: tail)
      (maximumDepth (first :: second :: tail)) (childFree (first :: second :: tail)) := by
  let members := first :: second :: tail
  let key := NodeKey.union (members.map Value.referenceOf)
  let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
  let after := (nodeStep key identify state).2
  let result := (nodeStep key identify state).1
  have built := makeUnion_available values state facts.coherent facts.cached available
  have output : Available after result := by simpa only [makeUnion, selected, ordinary, run] using built.2.2
  have later : Coherent after := by simpa only [makeUnion, selected, ordinary, run] using built.1
  have beforeInputs : Values state members := by simpa only [members, selected] using selected_available values state available
  have afterInputs : Values after members := by
    intro value member
    simpa only [makeUnion, selected, ordinary, run] using
      available_after_run (makeUnion values) state facts.coherent.valid (beforeInputs value member)
  obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state facts.coherent
    (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
  change NodeFields key actual result at fields
  have exactResult : ∃ entry, result = .union entry members (maximumDepth members) (childFree members) := by
    generalize found : result = value at fields output ⊢
    cases value with
    | empty | reference | node | mu => simp [NodeFields, key, muKey] at fields
    | union entry originals depth free =>
        have same := value_lists_equal after later members originals
          (fun value member => (afterInputs value member).resident)
          (fun value member => (output.children value member).resident) (NodeKey.union.inj fields.2.1)
        refine ⟨entry, ?_⟩
        simp only [NodeFields] at fields
        rw [same]
        rw [fields.2.2.1, fields.2.2.2]
  simpa only [makeUnion, selected, ordinary, run, members, result, key, identify] using exactResult

/-- The actual deleting branch reconstructs exactly the stripped canonical source operands. -/
theorem deleting [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (first second : Value Symbol Guard) (tail : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values)
    (selected : distinctNodes (values.flatMap unionMembers) = first :: second :: tail)
    (present : .reference name ∈ first :: second :: tail) :
    let original := run (makeUnion values) state
    run (withoutSelfReference name original.1) original.2 =
      run (makeUnion ((first :: second :: tail).filter (fun member => member.referenceOf != .ref name))) original.2 := by
  obtain ⟨entry, exactValue⟩ := union_readback values first second tail state facts available selected
    (ordinary_none name _ present)
  have hasSelf : ((first :: second :: tail).any (fun member => member.referenceOf == .ref name)) = true :=
    List.any_eq_true.mpr ⟨.reference name, present, by simp [Value.referenceOf]⟩
  dsimp only
  rw [exactValue]
  simp only [withoutSelfReference, hasSelf, ↓reduceIte]

/-- An absent reference leaves the source union result and complete returned state unchanged. -/
theorem absent [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (flat : Flat state) (available : Values state values)
    (missing : .reference name ∉ distinctNodes (values.flatMap unionMembers)) :
    withoutSelfReference name (run (makeUnion values) state).1 = .pure (run (makeUnion values) state).1 := by
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, selected, run, withoutSelfReference]
  | cons first rest =>
      cases rest with
      | nil =>
          have atomic := selected_atomic values state flat available first (by simp [selected])
          cases first <;> simp_all [Atomic, makeUnion, run, withoutSelfReference]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have inputs : Values state (first :: second :: tail) := by simpa [selected] using selected_available values state available
              have resident := ordinaryEdges_resident _ edges state facts.linked (fun value member => (inputs value member).resident) ordinary
              simpa only [makeUnion, selected, ordinary] using
                InternedFlatProbeCosts.makeNode_filter name edges state facts.coherent facts.linked resident
          | none =>
              obtain ⟨entry, exactValue⟩ := union_readback values first second tail state facts available selected ordinary
              rw [exactValue]
              exact withoutSelfReference_absent name entry _ _ _ (by simpa [selected] using missing)

/-- Canonical singleton self remains a bare reference and incurs no filtering effects. -/
theorem singleton_self [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (selected : distinctNodes (values.flatMap unionMembers) = [.reference name]) :
    withoutSelfReference name (run (makeUnion values) state).1 = .pure (.reference name) := by
  simp [makeUnion, selected, run, withoutSelfReference]

/-- Execute the exact source root filter from canonical operands while preserving the original union effects. -/
def fused [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) : Value Symbol Guard × State Symbol Guard :=
  let original := run (makeUnion values) state
  let selected := distinctNodes (values.flatMap unionMembers)
  match selected with
  | _ :: _ :: _ =>
      if selected.any (fun member => member.referenceOf == .ref name) then
        run (makeUnion (selected.filter (fun member => member.referenceOf != .ref name))) original.2
      else original
  | _ => original

/-- The fused equation is exact for every source normalization branch and complete cache readback. -/
theorem fusion [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (flat : Flat state) (available : Values state values) :
    let original := run (makeUnion values) state
    run (withoutSelfReference name original.1) original.2 = fused name values state := by
  dsimp only
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [fused, selected, makeUnion, run, withoutSelfReference]
  | cons first rest =>
      cases rest with
      | nil =>
          have atomic := selected_atomic values state flat available first (by simp [selected])
          cases first <;> simp_all [Atomic, fused, makeUnion, run, withoutSelfReference]
      | cons second tail =>
          cases hasSelf : (first :: second :: tail).any (fun member => member.referenceOf == .ref name) with
          | true =>
              obtain ⟨value, member, same⟩ := List.any_eq_true.mp hasSelf
              have sameValue := (referenceOf_self_iff name value).mp (beq_iff_eq.mp same)
              have present := sameValue ▸ member
              simpa only [fused, selected, hasSelf, ↓reduceIte] using deleting name values first second tail state facts available selected present
          | false =>
              have missing : .reference name ∉ distinctNodes (values.flatMap unionMembers) := by
                intro member
                have inList : Value.reference name ∈ first :: second :: tail := by simpa only [selected] using member
                have impossible : (first :: second :: tail).any (fun member => member.referenceOf == .ref name) = true :=
                  List.any_eq_true.mpr ⟨.reference name, inList, by simp [Value.referenceOf]⟩
                simp [hasSelf] at impossible
              rw [absent name values state facts flat available missing]
              simp [run, fused, selected, hasSelf]

end MicroCFTA.InternedUnionFilterFusion
