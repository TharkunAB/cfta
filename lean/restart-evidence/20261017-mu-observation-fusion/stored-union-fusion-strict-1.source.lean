import MicroCFTA.SourceCurrentStoredUnionFlattening
import MicroCFTA.SourceCurrentStoredCallSelection
import MicroCFTA.SourceCurrentStoredUnionWarm
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

/-!
# Actual union normalization and stored reconstruction

Initial ready data constructs both operation orders. Reconstructing the
normalized source has the same finite open observations as normalizing
the reconstructed source members. The theorem retains all actual heaps
and cache histories. It does not assert equal physical result values.
-/
namespace MicroCFTA.SourceCurrentStoredUnionFusion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentOpenObservations (Same)
open Language

/-- Actual warm normalization and reconstruction preserve every observation of the original member returns. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    (originals outputs : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (normalized result : Value Symbol Guard)
    (ready : Ready common) (available : Values common originals)
    (replacements : Replacements common environment)
    (actual : All₂ (fun original output => execute original environment common = .done output common)
      originals outputs)
    (made : run (makeUnion originals) common = (normalized, common))
    (called : execute normalized environment common = .done result common) :
    ∀ depth view, Same depth view [result] outputs := by
  obtain ⟨flatOutputs, flatCalls, flatSame⟩ := SourceCurrentStoredUnionFlattening.warm
    originals outputs environment common ready available replacements actual
  have flatAvailable : Values common (originals.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, present, included⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (available source present) value included
  obtain ⟨selectedOutputs, selectedCalls, _, selectedMembers⟩ := SourceCurrentStoredCallSelection.distinct
    environment common (originals.flatMap unionMembers) flatOutputs ready.semantic.1.normal.facts
      flatAvailable flatCalls
  have selectedAvailable : Values common (distinctNodes (originals.flatMap unionMembers)) :=
    fun value member => flatAvailable value (distinctNodes_member _ value member)
  have selectedSame := SourceCurrentStoredUnionWarm.warm environment common originals
    (distinctNodes (originals.flatMap unionMembers)) selectedOutputs normalized result ready
    selectedAvailable replacements rfl selectedCalls made called
  intro depth view
  exact (selectedSame depth view).trans
    ((SourceCurrentOpenObservationLists.of_members depth view selectedOutputs flatOutputs selectedMembers).trans
      (flatSame depth view).symm)

/-- Initial ready inputs construct both normalization orders and prove the same observations at every finite depth. -/
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
      Available final left ∧ Available final right ∧
      ∀ depth view, Same depth view [left] [right] := by
  let normalized := run (makeUnion originals) before
  have first : Keeps before normalized.2 :=
    SourceEqualityNativeDemandHeapPrimitives.work_keeps (makeUnion originals) before ready (.union originals available)
  have normalizedAvailable : Available normalized.2 normalized.1 :=
    (InternedNestedFacts.union_verified originals before ready.semantic.1.normal.facts available).result _ _ rfl
  obtain ⟨left, middle, called, second, leftAvailable, _⟩ :=
    SourceCurrentStoredReconstruction.execute normalized.1 environment normalized.2 first.ready
      normalizedAvailable (fun name value found => first.available value (replacements name value found))
  obtain ⟨outputs, memberState, calls, third, outputsAvailable⟩ :=
    SourceCurrentStoredUnionObservations.members originals environment middle second.ready
      (fun value member => second.available value (first.available value (available value member)))
      (fun name value found => second.available value (first.available value (replacements name value found)))
  let final := run (makeUnion outputs) memberState
  have fourth : Keeps memberState final.2 :=
    SourceEqualityNativeDemandHeapPrimitives.work_keeps (makeUnion outputs) memberState third.ready
      (.union outputs outputsAvailable)
  have rightAvailable : Available final.2 final.1 :=
    (InternedNestedFacts.union_verified outputs memberState third.ready.semantic.1.normal.facts outputsAvailable).result _ _ rfl
  have remaining := third.trans fourth
  have retained := first.trans (second.trans remaining)
  have normalizedWarm : run (makeUnion originals) final.2 = (normalized.1, final.2) :=
    InternedConstructorTemplates.replay (makeUnion originals) before final.2 ready.semantic.1.normal.facts.coherent.valid
      (second.trans remaining).growth
  have leftWarm : execute normalized.1 environment final.2 = .done left final.2 :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves normalized.1) [] normalized.1)
      ((leaves normalized.1).map (input environment)) normalized.2 final.2 left middle
      first.ready.semantic.1.normal.facts.coherent.valid called remaining.growth
  have callsWarm := SourceCurrentStoredCallsReplay.replay calls final.2
    second.ready.semantic.1.normal.facts.coherent.valid fourth.growth
  have leftSame := warm originals outputs environment final.2 normalized.1 left fourth.ready
    (fun value member => retained.available value (available value member))
    (fun name value found => retained.available value (replacements name value found))
    callsWarm normalizedWarm leftWarm
  refine ⟨normalized.1, normalized.2, left, middle, outputs, memberState, final.1, final.2,
    rfl, called, calls, rfl, first, second, third, fourth,
    remaining.available left leftAvailable, rightAvailable, ?_⟩
  intro depth view
  have rightSame := SourceCurrentOpenObservationConstructors.makeUnion_normalize depth memberState view
    third.ready.semantic.1.normal.facts third.ready.semantic.1.normal.live outputs outputsAvailable
  exact (leftSame depth view).trans rightSame.symm

end MicroCFTA.SourceCurrentStoredUnionFusion
