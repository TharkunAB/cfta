import MicroCFTA.InternedRootProfileNode
import MicroCFTA.InternedUnionFilterFusion

/-!
# Actual source union profiles

Flattening and ordered identity removal preserve opacity and the set of
literal references. The ordinary merge branch remains nonempty and
opaque. Complete union readback retains the exact canonical members.
-/
namespace MicroCFTA.InternedRootProfileUnion
open InternedConstructorTemplates InternedRootProfile InternedRootProfileLists InternedRootProfileNode
open InternedProbeProvenance InternedRecordCoherence InternedNestedFacts InternedNestedProvenance
open InternedEmptyNormalization InternedNonemptyRecords InternedLiveEdges InternedUnionFilterFusion
open InternedNormalizationFree InternedEdgeResidency
open InternedUnionDescendants

/-- An original operand that contributes a flattened value is not EmptyNode. -/
theorem flattened_source_nonempty (value member : Value Symbol Guard) (included : member ∈ unionMembers value) :
    value.referenceOf ≠ .empty := by
  cases value <;> simp_all [unionMembers, Value.referenceOf]

/-- Actual union construction preserves the full root profile up to set equivalence. -/
theorem makeUnion_profile [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (live : Live state) (proper : NonemptyRecords state)
    (inputs : Values state values) : Equivalent (profile (run (makeUnion values) state).1) (many values) := by
  have dedup := distinct_equivalent (values.flatMap unionMembers) state facts.coherent
    (fun value member => by
      obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp member
      exact (unionMembers_available source (inputs source included) value inner).resident)
  rw [flatten_profile] at dedup
  have exactProfile : profile (run (makeUnion values) state).1 = many (distinctNodes (values.flatMap unionMembers)) := by
    cases selected : distinctNodes (values.flatMap unionMembers) with
    | nil => simp [makeUnion, selected, run, profile, many]
    | cons first rest =>
        cases rest with
        | nil => simp [makeUnion, selected, run, many, combine_empty_right]
        | cons second tail =>
            cases ordinary : ordinaryEdges (first :: second :: tail) with
            | none =>
                obtain ⟨entry, returned⟩ := union_readback values first second tail state facts inputs selected ordinary
                rw [returned]
                simp only [profile]
            | some edges =>
                have members : Values state (first :: second :: tail) := by
                  simpa only [selected] using selected_available values state inputs
                have resident := ordinaryEdges_resident _ edges state facts.linked
                  (fun value member => (members value member).resident) ordinary
                have hidden : many (first :: second :: tail) = none := by
                  apply (many_none_iff _).mpr
                  obtain ⟨entry, own, depth, free, same, _⟩ := ordinaryEdges_contains _ edges ordinary first List.mem_cons_self
                  exact ⟨first, List.mem_cons_self, by rw [same]; simp only [profile]⟩
                have firstSelected : first ∈ distinctNodes (values.flatMap unionMembers) := by simp [selected]
                obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ first firstSelected)
                have nonempty := InternedEmptyNormalization.makeUnion_nonempty values state facts.coherent facts.linked live proper inputs
                  source included (flattened_source_nonempty source first inner)
                have nodeNonempty : (run (makeNode edges) state).1.referenceOf ≠ .empty := by
                  simpa only [makeUnion, selected, ordinary] using nonempty
                rw [hidden]
                simp only [makeUnion, selected, ordinary]
                rw [makeNode_shape edges state facts resident]
                simp [nodeNonempty]
  rw [exactProfile]
  exact dedup

end MicroCFTA.InternedRootProfileUnion
