import MicroCFTA.SourceFlatPruningRecursion
import MicroCFTA.SourcePruningEnumerationParkedLanguage
import MicroCFTA.EnumerationFlatSemantics

/-!
# Assignment meaning of actual flat recursion checks

The ordered result relation supplies a sufficient earlier check bound.
Each actual flat success has a related earlier success at that bound.
Repeated checks remove exactly the original suspended restrictions.
-/
namespace MicroCFTA.SourceFlatPruningRecursion
open Language EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

private theorem success_left
    {flatRows : List (Except Error (Bool × EnumerationFlatState.State Symbol EnumGuard))}
    {earlierRows : List (Except Error (Bool × EnumerationState.State Symbol EnumGuard))}
    {value : Bool} {after : EnumerationFlatState.State Symbol EnumGuard}
    (rows : EnumerationResultRelation.Results EnumerationFlatState.Related flatRows earlierRows)
    (observed : Except.ok (value, after) ∈ flatRows) :
    ∃ earlier, Except.ok (value, earlier) ∈ earlierRows ∧ EnumerationFlatState.Related after earlier := by
  induction rows with
  | nil => cases observed
  | cons first rest ih =>
      rcases List.mem_cons.mp observed with same | later
      · cases same
        cases first with
        | ok _value states => exact ⟨_, List.mem_cons_self, states⟩
      · obtain ⟨earlier, member, states⟩ := ih later
        exact ⟨earlier, List.mem_cons_of_mem _ member, states⟩

/-- An actual flat check preserves assignment meaning except for its explicitly removed bucket. -/
theorem checkRepeated_satisfies
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationFlatState.State Symbol EnumGuard)
    (earlier : EnumerationState.State Symbol EnumGuard)
    (related : EnumerationFlatState.Related before earlier)
    (ready : EnumerationDriver.Ready uv earlier)
    (stored : earlier.values[uv]? = some (.unenumerated (some handle) scs))
    (repeated : Bool)
    (observed : Except.ok (repeated, after) ∈ ExceptT.run (checkRepeated heap uv handle scs before)) :
    EnumerationFlatState.Satisfies language meaning assignment before ↔
      EnumerationFlatState.Satisfies language meaning assignment after ∧
        (repeated = true → ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) := by
  obtain ⟨fuel, stable⟩ := checkRepeated_stable related heap uv handle scs
  have rows := stable 0
  simp only [Nat.add_zero] at rows
  obtain ⟨earlierAfter, earlierObserved, afterRelated⟩ := success_left rows observed
  have beforeMeaning := EnumerationFlatState.related_satisfies related language meaning assignment
  have afterMeaning := EnumerationFlatState.related_satisfies afterRelated language meaning assignment
  cases repeated with
  | false =>
      have preserved := SourcePruningEnumerationRecursion.checkRepeated_false_satisfies heap
        language meaning assignment fuel uv handle scs earlier earlierAfter ready.safe.1.total earlierObserved
      simpa using beforeMeaning.symm.trans (preserved.symm.trans afterMeaning)
  | true =>
      have cleared := SourcePruningEnumerationRecursion.checkRepeated_true_satisfies heap
        language meaning assignment fuel uv handle scs earlier earlierAfter ready stored earlierObserved
      simpa using beforeMeaning.symm.trans (cleared.trans (and_congr afterMeaning Iff.rfl))

end MicroCFTA.SourceFlatPruningRecursion
