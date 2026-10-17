import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentOpenObservationLists

/-!
# Actual warm reconstruction of flattened union members

Each stored union supplies actual calls for its literal members. Empty
supplies no member. Flattening therefore retains all finite observations
of the original warm results in every fixed view. Nested Mu values remain
literal members, with their exact completed reconstruction calls.
-/
namespace MicroCFTA.SourceCurrentStoredUnionFlattening
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentOpenObservations (Same)
open Language

private theorem append {A B : Type} {relation : A → B → Prop}
    {first next : List A} {second last : List B}
    (left : All₂ relation first second) (right : All₂ relation next last) :
    All₂ relation (first ++ next) (second ++ last) := by
  induction left with
  | nil => exact right
  | cons pair rest ih => exact .cons pair ih

private theorem member [DecidableEq (EdgeKey Symbol Guard)]
    (original output : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common)
    (available : Available common original) (replacements : Replacements common environment)
    (actual : execute original environment common = .done output common) :
    ∃ values, All₂ (fun value result => execute value environment common = .done result common)
      (unionMembers original) values ∧ ∀ depth view, Same depth view [output] values := by
  cases original with
  | empty =>
      have same := (Outcome.done.inj
        ((SourceCurrentStoredUnionObservations.closed .empty environment common rfl).symm.trans actual)).1
      subst output
      refine ⟨[], .nil, ?_⟩
      intro depth view
      have observed := SourceCurrentOpenObservationConstructors.makeUnion_normalize depth common view
        ready.semantic.1.normal.facts ready.semantic.1.normal.live []
        (by intro value present; cases present)
      simpa only [makeUnion, List.flatMap_nil, distinctNodes, run] using observed
  | node entry rows level free =>
      exact ⟨[output], .cons actual .nil, fun depth view => Same.refl depth view [output]⟩
  | reference name =>
      exact ⟨[output], .cons actual .nil, fun depth view => Same.refl depth view [output]⟩
  | mu entry body cachedDepth ordinary =>
      exact ⟨[output], .cons actual .nil, fun depth view => Same.refl depth view [output]⟩
  | union entry originals level free =>
      obtain ⟨result, after, values, middle, called, calls, _, _, _, _, growth, observed⟩ :=
        SourceCurrentStoredUnionObservations.complete entry originals level free environment common ready
          available replacements
      obtain ⟨rfl, rfl⟩ := Outcome.done.inj (called.symm.trans actual)
      exact ⟨values, SourceCurrentStoredCallsReplay.replay calls _
        ready.semantic.1.normal.facts.coherent.valid growth, observed⟩

/-- Actual warm source calls derive all flattened member calls and preserve every finite open observation. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    (originals outputs : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common)
    (available : Values common originals) (replacements : Replacements common environment)
    (actual : All₂ (fun original output => execute original environment common = .done output common)
      originals outputs) :
    ∃ values, All₂ (fun original output => execute original environment common = .done output common)
      (originals.flatMap unionMembers) values ∧ ∀ depth view, Same depth view outputs values := by
  induction actual with
  | nil => exact ⟨[], .nil, fun depth view => Same.refl depth view []⟩
  | @cons original output originals outputs called rest ih =>
      obtain ⟨first, calls, observed⟩ := member original output environment common ready
        (available original List.mem_cons_self) replacements called
      obtain ⟨last, remaining, later⟩ := ih
        (fun value present => available value (List.mem_cons_of_mem _ present))
      refine ⟨first ++ last, append calls remaining, ?_⟩
      intro depth view
      exact SourceCurrentOpenObservationLists.append depth view [output] first outputs last
        (observed depth view) (later depth view)

end MicroCFTA.SourceCurrentStoredUnionFlattening
