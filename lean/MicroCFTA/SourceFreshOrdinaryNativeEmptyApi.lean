import MicroCFTA.SourceSizedDispatcher

/-!
# Exact empty language at the public native entry

The source EmptyNode branch returns an empty map before traversal.
Its complete query record has no class members, counts, or valid positions.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeEmptyApi
open Language SourceSizedDispatcher

/-- The complete public query record of the source's direct empty-map result. -/
def api : Api Symbol := ⟨fun _ => [], fun _ => 0, fun _ _ => none, fun _ => none⟩

/-- Every reference class of an empty row map is empty without child recursion. -/
theorem classes_empty [DecidableEq Symbol] (size : Nat) (root : State) :
    SourceSizedReference.classes (fun _ : State => ([] : List (Edge State Symbol))) size root = [] := by
  cases size <;> simp [SourceSizedReference.classes, SourceSizedReference.classOf, SourceSizedReference.nub, RefinementValidation.dedup]

/-- The direct empty query record equals the complete signed reference record. -/
theorem reference [DecidableEq Symbol] (root : State) :
    referenceApi (fun _ : State => ([] : List (Edge State Symbol))) root = api := by
  change Api.mk _ _ _ _ = Api.mk _ _ _ _
  congr 1
  · funext size
    simp [SourceSizedQueries.termsSigned, classes_empty]
  · funext size
    simp [SourceSizedQueries.countSigned, SourceSizedQueries.termsSigned, classes_empty]
  · funext size rank
    simp [SourceSizedQueries.unrankSigned, SourceSizedQueries.termsSigned, classes_empty]
  · funext term
    simp [SourceSizedQueries.rank, classes_empty, SizedRank.rankOf]

end MicroCFTA.SourceFreshOrdinaryNativeEmptyApi
