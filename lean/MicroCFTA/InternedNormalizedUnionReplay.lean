import MicroCFTA.InternedUnionFilterFusion
import MicroCFTA.InternedUnionNonemptyMembers
import MicroCFTA.InternedNonemptyRecords
import MicroCFTA.InternedRootAlternativeLists

/-!
# Exact requests from normalized union operands

Canonical source operands are flat, nonempty, and distinct by identity.
Constructing their union therefore repeats the same finite request.
Removing one bare reference preserves these normalization properties.
-/
namespace MicroCFTA.InternedNormalizedUnionReplay
open InternedConstructorTemplates InternedProbeProvenance InternedNonemptyRecords
open InternedNestedFacts InternedNestedProvenance InternedUnionNormalForm InternedUnionNonemptyMembers
open InternedUnionFilterFusion InternedRootAlternativeLists
open InternedBinderProtocol (Reference)

/-- Distinct source identities require no further first-identity removal. -/
theorem distinct_of_nodup (values : List (Value Symbol Guard))
    (unique : (values.map Value.referenceOf).Nodup) : distinctNodes values = values := by
  induction values with
  | nil => simp [distinctNodes]
  | cons first rest ih =>
      have parts := List.nodup_cons.mp unique
      have kept : rest.filter (fun value => value.referenceOf != first.referenceOf) = rest := by
        apply List.filter_eq_self.mpr
        intro value member
        apply bne_iff_ne.mpr
        intro same
        exact parts.1 (List.mem_map.mpr ⟨value, member, same⟩)
      rw [distinctNodes, kept, ih parts.2]

/-- Nonempty atomic values each contribute exactly themselves to source flattening. -/
theorem flattened (values : List (Value Symbol Guard))
    (atomic : ∀ value ∈ values, Atomic value) (nonempty : ∀ value ∈ values, MemberNonempty value) :
    values.flatMap unionMembers = values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have one : unionMembers first = [first] := by
        have a := atomic first List.mem_cons_self
        have n := nonempty first List.mem_cons_self
        cases first <;> simp_all [Atomic, MemberNonempty, Value.referenceOf, unionMembers]
      simp only [List.flatMap_cons, one, List.singleton_append,
        ih (fun value member => atomic value (List.mem_cons_of_mem _ member))
          (fun value member => nonempty value (List.mem_cons_of_mem _ member))]

/-- Every canonical operand is nonempty when the original inputs use normalized source records. -/
theorem selected_nonempty (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (proper : MembersNonempty state) (inputs : Values state values) :
    ∀ value ∈ distinctNodes (values.flatMap unionMembers), MemberNonempty value := by
  intro value member
  obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
  exact membersNonempty_members source (resident_membersNonempty state proper source (inputs source included).resident) value inner

/-- Reconstructing the canonical source operands executes the identical finite constructor request. -/
theorem makeUnion_selected (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (flat : Flat state) (proper : MembersNonempty state) (inputs : Values state values) :
    makeUnion (distinctNodes (values.flatMap unionMembers)) = makeUnion values := by
  unfold makeUnion
  rw [flattened _ (selected_atomic values state flat inputs) (selected_nonempty values state proper inputs),
    distinct_of_nodup _ (distinctNodes_nodup _)]

/-- Removing one local reference retains normalized source operands. -/
theorem stripped_normalized (name : Reference) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (flat : Flat state) (proper : MembersNonempty state) (inputs : Values state values) :
    distinctNodes ((remove name (distinctNodes (values.flatMap unionMembers))).flatMap unionMembers) =
      remove name (distinctNodes (values.flatMap unionMembers)) := by
  unfold remove
  rw [flattened _
    (fun value member => selected_atomic values state flat inputs value (List.mem_filter.mp member).1)
    (fun value member => selected_nonempty values state proper inputs value (List.mem_filter.mp member).1)]
  apply distinct_of_nodup
  exact (List.filter_sublist.map Value.referenceOf).nodup (distinctNodes_nodup _)

/-- Except for singleton self, filtering executes the stripped canonical request at the actual intermediate state. -/
theorem filtered_as_request [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (flat : Flat state) (proper : MembersNonempty state) (inputs : Values state values)
    (notSelf : distinctNodes (values.flatMap unionMembers) ≠ [.reference name]) :
    let original := run (makeUnion values) state
    run (withoutSelfReference name original.1) original.2 =
      run (makeUnion (remove name (distinctNodes (values.flatMap unionMembers)))) original.2 := by
  dsimp only
  by_cases present : .reference name ∈ distinctNodes (values.flatMap unionMembers)
  · cases selected : distinctNodes (values.flatMap unionMembers) with
    | nil => simp [selected] at present
    | cons first rest =>
        cases rest with
        | nil =>
            have same : .reference name = first := by simpa [selected] using present
            exact False.elim (notSelf (by simp [selected, same]))
        | cons second tail =>
            simpa only [selected, remove] using deleting name values first second tail state facts inputs selected
              (by simpa only [selected] using present)
  · rw [absent name values state facts flat inputs present]
    have unchanged : remove name (distinctNodes (values.flatMap unionMembers)) =
        distinctNodes (values.flatMap unionMembers) := by
      apply List.filter_eq_self.mpr
      intro value member
      apply bne_iff_ne.mpr
      intro same
      exact present ((referenceOf_self_iff name value).mp same ▸ member)
    rw [unchanged, makeUnion_selected values state flat proper inputs]
    exact (replay (makeUnion values) state (run (makeUnion values) state).2 facts.coherent.valid
      (grows_refl _)).symm

end MicroCFTA.InternedNormalizedUnionReplay
