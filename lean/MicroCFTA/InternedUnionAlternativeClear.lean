import MicroCFTA.InternedPairedSelfFilter
import MicroCFTA.InternedUnionFilterFusion

/-!
# Boundary absence in original source union alternatives

Constructing and filtering a source union can remove its own bare root
reference. Every other flattened operand retains all of its boundaries.
This theorem includes singleton collapse and the ordinary merge branch.
-/
namespace MicroCFTA.InternedUnionAlternativeClear
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedNestedConstruction
open InternedLiveEdges InternedUnionNormalForm InternedUnionRetention InternedBoundaryAtoms
open InternedObservedAbsence InternedUnionFilterFusion
open InternedBinderProtocol (Reference NodeRef)

/-- A clear normalized source union makes every original nonself root alternative clear. -/
theorem clear_alternative [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (live : Live state) (inputs : Values state values)
    (clear : Clear forbidden (run (withoutSelfReference name (run (makeUnion values) state).1)
      (run (makeUnion values) state).2).1)
    (value : Value Symbol Guard) (member : value ∈ values.flatMap unionMembers)
    (different : value ≠ .reference name) : Clear forbidden value := by
  have all : Values state (values.flatMap unionMembers) := by
    intro child included
    obtain ⟨source, original, inner⟩ := List.mem_flatMap.mp included
    exact unionMembers_available source (inputs source original) child inner
  have selected := distinctNodes_retains state facts.coherent _ (fun child included => (all child included).resident) value member
  by_cases own : .reference name ∈ distinctNodes (values.flatMap unionMembers)
  · cases normalized : distinctNodes (values.flatMap unionMembers) with
    | nil => simp [normalized] at own
    | cons first rest =>
        cases rest with
        | nil =>
            have same : value = first := by simpa [normalized] using selected
            have self : .reference name = first := by simpa [normalized] using own
            exact False.elim (different (same.trans self.symm))
        | cons second tail =>
            have present : .reference name ∈ first :: second :: tail := by simpa [normalized] using own
            rw [deleting name values first second tail state facts inputs normalized present] at clear
            have checked := union_verified values state facts inputs
            let after := (run (makeUnion values) state).2
            have afterFacts : Facts after := checked.facts
            have afterLive : Live after := makeUnion_live values state live
            have afterInputs : Values after ((first :: second :: tail).filter (fun child => child.referenceOf != .ref name)) := by
              intro child included
              have before : Available state child := selected_available values state inputs child (by
                simpa only [normalized] using (List.mem_filter.mp included).1)
              exact available_after_run (makeUnion values) state facts.coherent.valid before
            intro item included
            apply clear item
            apply (makeUnion_atom_iff _ after afterFacts.coherent afterFacts.cached afterFacts.linked afterLive afterInputs item).mpr
            exact ⟨value, (withoutSelfReference_members name _ value).mpr ⟨by simpa [normalized] using selected, different⟩, included⟩
  · rw [absent name values state facts flat inputs own] at clear
    obtain ⟨source, original, inner⟩ := List.mem_flatMap.mp member
    intro item included
    apply clear item
    exact makeUnion_atom values state facts.coherent facts.cached facts.linked live inputs source original item
      ((flatten_atom source item).mpr ⟨value, inner, included⟩)

end MicroCFTA.InternedUnionAlternativeClear
