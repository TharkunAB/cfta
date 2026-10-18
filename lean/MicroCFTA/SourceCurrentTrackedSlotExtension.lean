import MicroCFTA.SourceCurrentTrackedRootProfile
import MicroCFTA.SourceCurrentReaderReplacementSlots

/-!
# Fresh tracked markers through actual lexical slots

A finite resolved lexical support excludes the new marker. Extending the
tracked list then preserves each earlier slot relation. Fresh local names
can bind the same marker on both sides without changing old captures.
The result supplies input premises for a later source binder induction.
-/
namespace MicroCFTA.SourceCurrentTrackedSlotExtension
open InternedConstructorTemplates InternedRootProfile
open InternedStoredSubstitution (Environment input)
open InternedBinderProtocol (Reference)
open SourceCurrentTrackedRootProfile (Related observe mask mask_cons_fresh)
open SourceCurrentReaderReplacementSlots (Slot Paired)
open SourceCurrentStoredMuBinderChildLineage (bind)

/-- A marker absent from both resolved profiles preserves their exact comparison. -/
theorem related (marker : Reference) (markers : List Reference) (first second : Value Symbol Guard)
    (firstFresh : marker ∉ (profile first).getD []) (secondFresh : marker ∉ (profile second).getD []) :
    Related (marker :: markers) first second ↔ Related markers first second := by
  unfold Related observe
  rw [mask_cons_fresh marker markers _ firstFresh,mask_cons_fresh marker markers _ secondFresh]

/-- Exact finite resolved lexical freshness extends the tracked list for every paired slot. -/
theorem paired (marker : Reference) (markers : List Reference)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (slots : Paired (Related markers) first second left right)
    (firstFresh : ∀ value ∈ left, marker ∉ (profile (input first value)).getD [])
    (secondFresh : ∀ value ∈ right, marker ∉ (profile (input second value)).getD []) :
    Paired (Related (marker :: markers)) first second left right := by
  induction slots with
  | nil => exact .nil
  | @cons a b left right slot tail ih =>
      refine .cons ?_ (ih (fun value member => firstFresh value (List.mem_cons_of_mem _ member))
        (fun value member => secondFresh value (List.mem_cons_of_mem _ member)))
      cases a <;> cases b
      all_goals try {cases slot}
      case reference.reference a b =>
        exact (related marker markers _ _ (firstFresh _ List.mem_cons_self) (secondFresh _ List.mem_cons_self)).mpr slot
      all_goals exact slot

/-- Fresh lexical local names bind a shared tracked marker and retain all earlier paired captures. -/
theorem bind_marker (marker : Reference) (markers : List Reference)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (slots : Paired (Related markers) first second left right)
    (firstFresh : ∀ value ∈ left, marker ∉ (profile (input first value)).getD [])
    (secondFresh : ∀ value ∈ right, marker ∉ (profile (input second value)).getD [])
    (firstName secondName : Reference)
    (firstLocalFresh : ∀ value ∈ left, firstName ∉ value.free)
    (secondLocalFresh : ∀ value ∈ right, secondName ∉ value.free) :
    Paired (Related (marker :: markers))
      (bind firstName (.reference marker) first) (bind secondName (.reference marker) second)
      (.reference firstName :: left) (.reference secondName :: right) :=
  SourceCurrentReaderReplacementSlots.extend (Related (marker :: markers)) first second left right
    (paired marker markers first second left right slots firstFresh secondFresh) firstName secondName
    (.reference marker) (.reference marker) (Related.refl _ _) firstLocalFresh secondLocalFresh

end MicroCFTA.SourceCurrentTrackedSlotExtension
