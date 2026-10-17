import MicroCFTA.InternedNormalizedUnionReplay
import MicroCFTA.InternedUnionReference
import MicroCFTA.SourceCurrentNativeCallbackErasure

/-!
# Exact root erasure through actual union normalization

The source filter retains a bare self reference. Erasing that final case
gives the same complete pair as the stripped canonical union request.
The equation retains all effects of the original union construction.
-/
namespace MicroCFTA.SourceCurrentNativeRootErasure
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedRootAlternativeLists InternedNormalizedUnionReplay
open SourceCurrentNativeCallbackErasure (eraseSelf)
open InternedBinderProtocol (Reference)

/-- Erasure retains every result other than its supplied bare reference. -/
theorem erase_of_ne (name : Reference) (value : Value Symbol Guard)
    (different : value ≠ .reference name) : eraseSelf name value = value := by
  unfold eraseSelf
  split
  · rename_i same
    exact False.elim (different ((referenceOf_self_iff name value).mp same))
  · rfl

/-- Filtering and final bare-self erasure execute the stripped canonical request at the actual union return. -/
theorem union_request [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state values) :
    let original := run (makeUnion values) state
    let filtered := run (withoutSelfReference name original.1) original.2
    (eraseSelf name filtered.1, filtered.2) =
      run (makeUnion (remove name (distinctNodes (values.flatMap unionMembers)))) original.2 := by
  dsimp only
  by_cases singleton : distinctNodes (values.flatMap unionMembers) = [.reference name]
  · simp [makeUnion, singleton, run, withoutSelfReference, eraseSelf, remove, Value.referenceOf, distinctNodes]
  · have checked := union_verified values state normal.facts inputs
    have different : (run (makeUnion values) state).1 ≠ .reference name :=
      fun same => singleton ((InternedUnionReference.normalized_singleton_iff name values state
        normal.facts.coherent).mp same)
    have filteredDifferent : (run (withoutSelfReference name (run (makeUnion values) state).1)
        (run (makeUnion values) state).2).1 ≠ .reference name := by
      intro same
      exact different ((InternedFilterSelfReference.filter_self_iff name _ _ checked.facts.coherent
        (InternedUnionNormalForm.makeUnion_flat values state normal.flat inputs)
        (checked.result _ _ rfl)).mp same)
    rw [erase_of_ne name _ filteredDifferent]
    exact filtered_as_request name values state normal.facts normal.flat normal.members inputs singleton

end MicroCFTA.SourceCurrentNativeRootErasure
