import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.MergedFreshOrdinaryUnionOrigins

/-!
# Complete row origins through actual callback root normalization

Bare references have no constructor origin. Removing a bare local and
normalizing the remaining union therefore preserves every complete row.
The origin view can be any heap. The input normalization facts concern only
the actual heap where the filter runs.
-/
namespace MicroCFTA.SourceCurrentNativeCallbackRowOrigins
open InternedConstructorTemplates InternedProbeProvenance InternedStoredMuOrigins
open InternedNestedProvenance (Values)
open InternedRootAlternativeLists (remove)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open MergedFreshOrdinaryGraph
open InternedBinderProtocol (Reference)

private theorem reference_no_origin [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (own : Reference) (row : EdgeValue Symbol Guard) :
    ¬ Origin view [.reference own] row := by
  intro origin
  have impossible := MergedFreshOrdinaryExposureCoverage.origin_terminal view (.reference own) rfl row origin
  cases impossible

/-- Bare-self erasure preserves every complete constructor origin at any view heap. -/
theorem erase_self [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (own : Reference) (value : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    Origin view [eraseSelf own value] row ↔ Origin view [value] row := by
  unfold eraseSelf
  split
  · rename_i same
    have bare := (referenceOf_self_iff own value).mp same
    subst value
    exact iff_of_false (origin_empty view row) (reference_no_origin view own row)
  · rfl

/-- The literal root filter retains exact row records through union normalization. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (before view : State Symbol Guard)
    (own : Reference) (value : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (normal : Normal before) (available : Available before value) :
    Origin view [(run (withoutSelfReference own value) before).1] row ↔ Origin view [value] row := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      by_cases selected : members.any (fun member => member.referenceOf == .ref own) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        have inputs : Values before (remove own members) := by
          intro child included
          exact available.children child (List.mem_filter.mp included).1
        apply (MergedFreshOrdinaryUnionOrigins.union_origins before view normal.facts normal.live
          (remove own members) inputs row).trans
        rw [origin_union]
        constructor
        · rintro ⟨child, included, origin⟩
          exact ⟨child, (List.mem_filter.mp included).1, origin⟩
        · rintro ⟨child, included, origin⟩
          refine ⟨child, List.mem_filter.mpr ⟨included, bne_iff_ne.mpr ?_⟩, origin⟩
          intro same
          have bare := (referenceOf_self_iff own child).mp same
          exact reference_no_origin view own row (bare ▸ origin)
      · have missing : members.any (fun member => member.referenceOf == .ref own) = false :=
          Bool.eq_false_iff.mpr selected
        simp only [withoutSelfReference, missing, Bool.false_eq_true, ↓reduceIte, run]

end MicroCFTA.SourceCurrentNativeCallbackRowOrigins
