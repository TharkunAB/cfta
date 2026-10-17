import MicroCFTA.SourceCurrentStoredUnionSurvival
import MicroCFTA.SourceCurrentLiteralOrdinaryParts
import MicroCFTA.SourceCurrentStoredUnionLiteralParts
import MicroCFTA.SourceCurrentLiteralFilterParts
import MicroCFTA.SourceCurrentStoredUnionEmpty
import MicroCFTA.SourceCurrentOrdinaryObservationEmpty
import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.InternedNormalizedUnionReplay

/-!
# Literal provenance of actual union reconstruction

Both union-normalization orders retain the same literal reference and Mu
atoms and the same complete ordinary rows. Initial data supplies all calls.
The proof also retains physical empty agreement and finite observations.
-/
namespace MicroCFTA.SourceCurrentLiteralUnionFusion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentOpenObservationSurvival (Related)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open Language

private theorem flatten_atoms (values : List (Value Symbol Guard))
    (single : ∀ value ∈ values, unionMembers value = [value]) : values.flatMap unionMembers = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.flatMap_cons,single value List.mem_cons_self,List.singleton_append]
      exact congrArg (List.cons value) (ih (fun value member => single value (List.mem_cons_of_mem _ member)))

private theorem selected_parts [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (originalInputs selected outputs : List (Value Symbol Guard))
    (normalized result : Value Symbol Guard) (ready : Ready common) (originalAvailable : Values common originalInputs)
    (replacements : Replacements common environment)
    (selection : distinctNodes (originalInputs.flatMap unionMembers) = selected)
    (paired : All₂ (fun original output => execute original environment common = .done output common) selected outputs)
    (made : run (makeUnion originalInputs) common = (normalized,common))
    (called : execute normalized environment common = .done result common) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  have available : Values common selected := by
    simpa only [selection] using InternedUnionFilterFusion.selected_available originalInputs common originalAvailable
  cases selected with
  | nil =>
      cases paired
      have value : normalized = .empty := by
        have same := congrArg Prod.fst made
        simpa only [makeUnion,selection,run] using same.symm
      subst normalized
      have same := (Outcome.done.inj
        (called.symm.trans (SourceCurrentStoredUnionObservations.closed .empty environment common rfl))).1
      subst result
      constructor
      · intro atom
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro ⟨_, impossible, _⟩; cases impossible)
      · intro row
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro ⟨_, impossible, _⟩; cases impossible)
  | cons first rest =>
      cases rest with
      | nil =>
          cases paired with
          | cons head tail =>
              cases tail
              have value : normalized = first := by
                have same := congrArg Prod.fst made
                simpa only [makeUnion,selection,run] using same.symm
              subst normalized
              have same := (Outcome.done.inj (called.symm.trans head)).1
              subst result
              simp only [List.mem_singleton, exists_eq_left, implies_true, and_self]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first::second::tail) with
          | some rows =>
              have allNodes : ∀ value ∈ first::second::tail, ∃ entry edges level free,
                  value = .node entry edges level free := by
                intro value member
                obtain ⟨entry,edges,level,free,same,_⟩ :=
                  InternedUnionDescendants.ordinaryEdges_contains _ rows ordinary value member
                exact ⟨entry,edges,level,free,same⟩
              have flat := flatten_atoms (first::second::tail) (by
                intro value member
                obtain ⟨entry,edges,level,free,rfl⟩ := allNodes value member
                rfl)
              have distinct : distinctNodes (first::second::tail) = first::second::tail := by
                apply InternedNormalizedUnionReplay.distinct_of_nodup
                rw [←selection]
                exact InternedNonemptyRecords.distinctNodes_nodup _
              have sameWork : makeUnion (first::second::tail) = makeUnion originalInputs := by
                simp only [makeUnion,flat,distinct,selection]
              exact SourceCurrentLiteralOrdinaryParts.warm ready available replacements
                (fun value member => by obtain ⟨entry,edges,level,free,rfl⟩ := allNodes value member; trivial)
                paired (by rw [sameWork]; exact made) called
          | none =>
              obtain ⟨entry, shape⟩ := InternedUnionFilterFusion.union_readback originalInputs first second tail common
                ready.semantic.1.normal.facts originalAvailable selection ordinary
              rw [made] at shape
              dsimp only at shape
              have normalizedAvailable := (InternedNestedFacts.union_verified originalInputs common
                ready.semantic.1.normal.facts originalAvailable).result normalized common
                (by simp only [InternedNestedConstruction.work, made])
              rw [shape] at normalizedAvailable called
              exact SourceCurrentStoredUnionLiteralParts.warm entry (first::second::tail)
                (maximumDepth (first::second::tail)) (childFree (first::second::tail)) environment common result outputs
                ready normalizedAvailable replacements called paired

/-- Actual warm normalization and reconstruction retain exact literal atoms and rows. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    (originals outputs : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (normalized result : Value Symbol Guard)
    (ready : Ready common) (available : Values common originals)
    (replacements : Replacements common environment)
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (made : run (makeUnion originals) common = (normalized, common))
    (called : execute normalized environment common = .done result common) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  obtain ⟨flattened, flatCalls, flatLiteral, flatRows, _⟩ := SourceCurrentStoredUnionLiteralParts.flatten_warm
    originals outputs environment common ready available replacements actual
  have flatAvailable : Values common (originals.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, present, included⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (available source present) value included
  obtain ⟨selectedOutputs, selectedCalls, _, members⟩ := SourceCurrentStoredCallSelection.distinct
    environment common (originals.flatMap unionMembers) flattened ready.semantic.1.normal.facts flatAvailable flatCalls
  have selectedParts := selected_parts environment common originals (distinctNodes (originals.flatMap unionMembers))
    selectedOutputs normalized result ready available replacements rfl selectedCalls made called
  have selectedFlat (predicate : Value Symbol Guard → Prop) :
      (∃ value ∈ selectedOutputs, predicate value) ↔ ∃ value ∈ flattened, predicate value := by
    constructor
    · rintro ⟨value, member, part⟩
      exact ⟨value, (members value).mp member, part⟩
    · rintro ⟨value, member, part⟩
      exact ⟨value, (members value).mpr member, part⟩
  exact ⟨fun atom => ((selectedParts.1 atom).trans (selectedFlat (fun value => Literal value atom))).trans
    (flatLiteral atom).symm,
    fun row => ((selectedParts.2 row).trans (selectedFlat (fun value => Row value row))).trans (flatRows row).symm⟩

private theorem outputs_available [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (ready : Ready common)
    {originals outputs : List (Value Symbol Guard)} (available : Values common originals)
    (replacements : Replacements common environment)
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    Values common outputs := by
  induction paired with
  | nil => intro value member; cases member
  | @cons original output originals outputs actual rest ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | later
      · exact (InternedFreshOrdinaryFacts.build_verified (encode (leaves original) [] original)
          ((leaves original).map (input environment)) common ready.semantic.1.normal.facts
          (InternedStoredSubstitution.inputs_available original environment common
            (available original List.mem_cons_self) replacements)).result _ common actual
      · exact ih (fun value member => available value (List.mem_cons_of_mem _ member)) value later

/-- Initial data constructs both normalization orders with exact literal parts and physical observation agreement. -/
theorem initial [DecidableEq (EdgeKey Symbol Guard)]
    (originals : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before)
    (available : Values before originals) (replacements : Replacements before environment) :
    ∃ normalized normalizedState left middle outputs memberState right final,
      run (makeUnion originals) before = (normalized, normalizedState) ∧
      execute normalized environment normalizedState = .done left middle ∧
      Calls environment originals middle outputs memberState ∧
      run (makeUnion outputs) memberState = (right, final) ∧
      Keeps before normalizedState ∧ Keeps normalizedState middle ∧
      Keeps middle memberState ∧ Keeps memberState final ∧
      Available final left ∧ Available final right ∧ Related left right ∧ SameParts left right ∧
      ∀ name, SameParts (run (withoutSelfReference name left) final).1
        (run (withoutSelfReference name right) final).1 := by
  obtain ⟨normalized, normalizedState, left, middle, outputs, memberState, right, final,
    made, called, calls, joined, first, second, third, fourth, leftAvailable, rightAvailable, observed⟩ :=
    SourceCurrentStoredUnionSurvival.initial originals environment before ready available replacements
  have remaining := third.trans fourth
  have retained := first.trans (second.trans remaining)
  have normalizedWarm : run (makeUnion originals) final = (normalized, final) := by
    have repeated := InternedConstructorTemplates.replay (makeUnion originals) before final
      ready.semantic.1.normal.facts.coherent.valid (by simpa only [made] using (second.trans remaining).growth)
    simpa only [made] using repeated
  have calledWarm : execute normalized environment final = .done left final :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves normalized) [] normalized)
      ((leaves normalized).map (input environment)) normalizedState final left middle
      first.ready.semantic.1.normal.facts.coherent.valid called remaining.growth
  have paired := SourceCurrentStoredCallsReplay.replay calls final
    second.ready.semantic.1.normal.facts.coherent.valid fourth.growth
  have finalAvailable : Values final originals := fun value member => retained.available value (available value member)
  have finalReplacements : Replacements final environment :=
    fun name value found => retained.available value (replacements name value found)
  have leftParts := warm originals outputs environment final normalized left fourth.ready
    finalAvailable finalReplacements paired normalizedWarm calledWarm
  have outputAvailable := outputs_available environment final fourth.ready finalAvailable finalReplacements paired
  have joinedWarm : run (makeUnion outputs) final = (right, final) := by
    have repeated := InternedConstructorTemplates.replay (makeUnion outputs) memberState final
      third.ready.semantic.1.normal.facts.coherent.valid (by simpa only [joined] using grows_refl final)
    simpa only [joined] using repeated
  have rightLiteral := SourceCurrentLiteralUnionParts.literal final fourth.ready.semantic.1.normal.facts
    outputs outputAvailable
  have rightRows := SourceCurrentLiteralUnionParts.row final fourth.ready.semantic.1.normal.facts
    fourth.ready.semantic.1.normal.live outputs outputAvailable
  rw [joinedWarm] at rightLiteral rightRows
  have parts : SameParts left right :=
    ⟨fun atom => (leftParts.1 atom).trans (rightLiteral atom).symm,
      fun row => (leftParts.2 row).trans (rightRows row).symm⟩
  exact ⟨normalized, normalizedState, left, middle, outputs, memberState, right, final,
    made, called, calls, joined, first, second, third, fourth, leftAvailable, rightAvailable,
    observed, parts, fun name => SourceCurrentLiteralFilterParts.congr final final
      fourth.ready.semantic.1.normal fourth.ready.semantic.1.normal name left right
      leftAvailable rightAvailable parts.1 parts.2⟩

end MicroCFTA.SourceCurrentLiteralUnionFusion
