import MicroCFTA.SourcePruningEnumerationRecursionOrder
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Assignment meaning of actual recursion parking

Parking retains the native handle and removes the suspended bucket.
The original assignment holds exactly when the parked assignment holds
and every removed suspended constraint holds at the selected variable.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] recursionMonadList

/-- Clearing a stored bucket removes exactly its suspended assignment restrictions. -/
theorem clear_satisfies
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol EnumGuard)
    (uv : Nat) (node : Option Nat) (scs : List Suspended)
    (stored : before.values[uv]? = some (.unenumerated node scs))
    (written : Success (setValue uv (.unenumerated node [])) before () after) :
    Satisfies language meaning assignment before ↔
      Satisfies language meaning assignment after ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  have bound : uv < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have oldSlot : heap language before.values uv = slot language (.unenumerated node scs) := by
    simp only [heap, stored, Option.getD_some]
  have oldMeaning : slotSatisfies assignment uv (heap language before.values uv) ↔
      permits (node.map language) (assignment uv) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    simp only [oldSlot, slot, slotSatisfies, List.forall_mem_map]
  have clearedMeaning : slotSatisfies assignment uv (slot language (.unenumerated node [])) ↔
      permits (node.map language) (assignment uv) := by
    simp [slot, slotSatisfies]
  have heapSame : heap language after.values =
      setSlot (heap language before.values) uv (slot language (.unenumerated node [])) := by
    rw [shape]
    exact heap_set language before.values uv _ bound
  constructor
  · intro original
    obtain ⟨domain, suspended⟩ := oldMeaning.mp (original.1.2 uv)
    refine ⟨⟨⟨by simpa only [shape] using original.1.1, ?_⟩,
      by simpa only [shape] using original.2⟩, suspended⟩
    rw [heapSame]
    intro other
    by_cases same : other = uv
    · subst other
      simp only [setSlot]
      exact clearedMeaning.mpr domain
    · simpa only [setSlot, ite_eq_right same] using original.1.2 other
  · rintro ⟨parked, suspended⟩
    refine ⟨⟨by simpa only [shape] using parked.1.1, ?_⟩,
      by simpa only [shape] using parked.2⟩
    intro other
    by_cases same : other = uv
    · subst other
      have domain : permits (node.map language) (assignment uv) := by
        apply clearedMeaning.mp
        simpa only [heapSame, setSlot, ite_true] using parked.1.2 uv
      exact oldMeaning.mpr ⟨domain, suspended⟩
    · simpa only [heapSame, setSlot, ite_eq_right same] using parked.1.2 other

/-- An actual repeated check drops exactly the selected bucket's suspended restrictions. -/
theorem checkRepeated_true_satisfies
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv handle : Nat) (scs : List Suspended)
    (before after : State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (observed : Success (checkRepeated heap fuel uv handle scs) before true after) :
    Satisfies language meaning assignment before ↔
      Satisfies language meaning assignment after ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨same, _safe, _counter, _protected⟩ := EnumerationDriver.representative_root fuel uv root
          before resolved ready.safe ready.inside ready.root resolution
        subst root
        have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨rfl, rfl⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, rfl⟩ := (success_pure true true cleared after).mp returned
          have resolvedStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
            simpa only [frame.values] using stored
          exact (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment
            before resolved frame).symm.trans
            (clear_satisfies language meaning assignment resolved cleared uv (some handle) scs resolvedStored written)
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [checkRepeated, decoded, boundary, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible

/-- An actual nonrepeated check preserves all complete assignments. -/
theorem checkRepeated_false_satisfies
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv handle : Nat) (scs : List Suspended)
    (before after : State Symbol EnumGuard) (total : UnionFind.Total before.representatives)
    (observed : Success (checkRepeated heap fuel uv handle scs) before false after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before :=
  SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment before after
    (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap fuel uv handle scs
      before after total observed)

end MicroCFTA.SourcePruningEnumerationRecursion
