import MicroCFTA.SourceCurrentLiteralUnionFusion

/-!
# Actual reconstruction after literal root filtering

Initial ready inputs construct the filter and the stored reconstruction.
They also construct ordered calls on the retained original alternatives.
Both schedules have the same exact literal atoms and ordinary rows.
This result does not compare two different Mu callback writers.
-/
namespace MicroCFTA.SourceCurrentStoredFilterReconstruction
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open Language

/-- Only a union root removes the literal self alternative. Bare self remains. -/
def retained (own : Reference) : Value Symbol Guard → List (Value Symbol Guard)
  | .union _ members _ _ => members.filter (fun value => value.referenceOf != .ref own)
  | value => unionMembers value

private theorem retained_available (own : Reference) (raw : Value Symbol Guard)
    (state : State Symbol Guard) (available : Available state raw) :
    Values state (retained own raw) := by
  cases raw with
  | union entry members level free =>
      intro value member
      exact available.children value (List.mem_filter.mp member).1
  | empty | reference | node | mu =>
      exact unionMembers_available _ available

private theorem filter_keeps [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (raw : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before raw) : Keeps before (run (withoutSelfReference own raw) before).2 := by
  cases raw with
  | empty | reference | node | mu => exact SourceEqualityRequiredCache.pure_keeps before ready
  | union entry members level free =>
      by_cases chosen : members.any (fun value => value.referenceOf == .ref own) = true
      · simp only [withoutSelfReference, chosen, ↓reduceIte]
        exact (SourceEqualityNativeDemandHeapPrimitives.union _ before ready
          (fun value member => available.children value (List.mem_filter.mp member).1)).1
      · simp only [withoutSelfReference, chosen, Bool.false_eq_true, ↓reduceIte, run]
        exact SourceEqualityRequiredCache.pure_keeps before ready

private theorem warm_parts [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (raw filtered result : Value Symbol Guard) (outputs : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (ready : Ready common) (available : Available common raw)
    (replacements : Replacements common environment)
    (filteredActual : run (withoutSelfReference own raw) common = (filtered, common))
    (called : execute filtered environment common = .done result common)
    (paired : All₂ (fun original output => execute original environment common = .done output common)
      (retained own raw) outputs) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  cases raw with
  | empty =>
      cases paired
      have shape : filtered = .empty := (congrArg Prod.fst filteredActual).symm
      subst filtered
      have same := (Outcome.done.inj (called.symm.trans
        (SourceCurrentStoredUnionObservations.closed .empty environment common rfl))).1
      subst result
      constructor
      · intro atom
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro ⟨_, impossible, _⟩; cases impossible)
      · intro row
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro ⟨_, impossible, _⟩; cases impossible)
  | reference | node | mu =>
      cases paired with
      | cons head tail =>
          cases tail
          have same := (Outcome.done.inj (called.symm.trans (by
            have shape := congrArg Prod.fst filteredActual
            simp only [withoutSelfReference, run] at shape
            rw [←shape]
            exact head))).1
          subst result
          simp only [List.mem_singleton, exists_eq_left, implies_true, and_self]
  | union entry members level free =>
      by_cases chosen : members.any (fun value => value.referenceOf == .ref own) = true
      · have made : run (makeUnion (retained own (.union entry members level free))) common =
            (filtered, common) := by
          simpa only [retained, withoutSelfReference, chosen, ↓reduceIte] using filteredActual
        exact SourceCurrentLiteralUnionFusion.warm _ outputs environment common filtered result ready
          (retained_available own _ common available) replacements paired made called
      · have retainedSame : retained own (.union entry members level free) = members := by
          apply List.filter_eq_self.mpr
          intro value member
          apply bne_iff_ne.mpr
          intro same
          exact chosen (List.any_eq_true.mpr ⟨value, member, beq_iff_eq.mpr same⟩)
        rw [retainedSame] at paired
        have shape : filtered = .union entry members level free := by
          have same := congrArg Prod.fst filteredActual
          simpa only [withoutSelfReference, chosen, Bool.false_eq_true, ↓reduceIte, run] using same.symm
        subst filtered
        exact SourceCurrentStoredUnionLiteralParts.warm entry members level free environment common result outputs
          ready available replacements called paired

/-- Initial data constructs filtered reconstruction and the retained-member schedule with exact root parts. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (own : Reference) (raw : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before raw) (replacements : Replacements before environment) :
    ∃ filtered filterHeap left middle outputs memberHeap right final,
      run (withoutSelfReference own raw) before = (filtered, filterHeap) ∧
      execute filtered environment filterHeap = .done left middle ∧
      Calls environment (retained own raw) middle outputs memberHeap ∧
      run (makeUnion outputs) memberHeap = (right, final) ∧
      Keeps before filterHeap ∧ Keeps filterHeap middle ∧ Keeps middle memberHeap ∧ Keeps memberHeap final ∧
      Available final left ∧ Available final right ∧ SameParts left right := by
  let filtered := run (withoutSelfReference own raw) before
  have first : Keeps before filtered.2 := filter_keeps own raw before ready available
  have filteredAvailable : Available filtered.2 filtered.1 :=
    (InternedNestedFacts.filter_verified own raw before ready.semantic.1.normal.facts available).result _ _ rfl
  obtain ⟨left, middle, called, second, leftAvailable, _⟩ :=
    SourceCurrentStoredReconstruction.execute filtered.1 environment filtered.2 first.ready filteredAvailable
      (fun name value found => first.available value (replacements name value found))
  obtain ⟨outputs, memberHeap, calls, third, outputsAvailable⟩ :=
    SourceCurrentStoredUnionObservations.members (retained own raw) environment middle second.ready
      (fun value member => second.available value
        (first.available value (retained_available own raw before available value member)))
      (fun name value found => second.available value (first.available value (replacements name value found)))
  let final := run (makeUnion outputs) memberHeap
  have fourth := SourceEqualityNativeDemandHeapPrimitives.union outputs memberHeap third.ready outputsAvailable
  have remaining := third.trans fourth.1
  have whole := first.trans (second.trans remaining)
  have rawAvailable : Available final.2 raw := whole.available raw available
  have finalReplacements : Replacements final.2 environment :=
    fun name value found => whole.available value (replacements name value found)
  have filteredWarm : run (withoutSelfReference own raw) final.2 = (filtered.1, final.2) :=
    InternedConstructorTemplates.replay (withoutSelfReference own raw) before final.2
      ready.semantic.1.normal.facts.coherent.valid (second.trans remaining).growth
  have calledWarm : execute filtered.1 environment final.2 = .done left final.2 :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves filtered.1) [] filtered.1)
      ((leaves filtered.1).map (input environment)) filtered.2 final.2 left middle
      first.ready.semantic.1.normal.facts.coherent.valid called remaining.growth
  have paired := SourceCurrentStoredCallsReplay.replay calls final.2
    second.ready.semantic.1.normal.facts.coherent.valid fourth.1.growth
  have parts := warm_parts own raw filtered.1 left outputs environment final.2 fourth.1.ready
    rawAvailable finalReplacements filteredWarm calledWarm paired
  have joinedWarm : run (makeUnion outputs) final.2 = (final.1, final.2) :=
    InternedConstructorTemplates.replay (makeUnion outputs) memberHeap final.2
      third.ready.semantic.1.normal.facts.coherent.valid (grows_refl final.2)
  have outputAvailable : Values final.2 outputs :=
    fun value member => fourth.1.available value (outputsAvailable value member)
  have literalParts := SourceCurrentLiteralUnionParts.literal final.2 fourth.1.ready.semantic.1.normal.facts
    outputs outputAvailable
  have rowParts := SourceCurrentLiteralUnionParts.row final.2 fourth.1.ready.semantic.1.normal.facts
    fourth.1.ready.semantic.1.normal.live outputs outputAvailable
  rw [joinedWarm] at literalParts rowParts
  exact ⟨filtered.1, filtered.2, left, middle, outputs, memberHeap, final.1, final.2,
    rfl, called, calls, rfl, first, second, third, fourth.1,
    remaining.available left leftAvailable, fourth.2,
    (fun atom => (parts.1 atom).trans (literalParts atom).symm),
    fun row => (parts.2 row).trans (rowParts row).symm⟩

end MicroCFTA.SourceCurrentStoredFilterReconstruction
