import MicroCFTA.SourceCurrentStoredMuTrackedProfile

/-!
# Fresh markers for finite resolved root profiles

The marker exceeds every ordinary reference in the tracked names and in
the actual resolved value profiles. The choice needs no reader invariant.
Ordinary marker references are available in every reader.
-/
namespace MicroCFTA.SourceCurrentTrackedMarkerChoice
open InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile)
open InternedStoredSubstitution (Environment leaves input)
open InternedFreshOrdinaryConstruction (freeBound freeBound_lt)

/-- Choose an ordinary marker outside all supplied names and actual root profiles. -/
def choose (markers : List Reference) (values : List (Value Symbol Guard)) : Reference :=
  .uninterned (freeBound (markers ++ values.flatMap (fun value => (profile value).getD [])))

/-- The chosen marker is available and absent from every supplied root profile. -/
theorem fresh (markers : List Reference) (values : List (Value Symbol Guard))
    (reader : State Symbol Guard) :
    Available reader (.reference (choose markers values)) ∧
    choose markers values ∉ markers ∧
    ∀ value ∈ values, choose markers values ∉ (profile value).getD [] := by
  let names := markers ++ values.flatMap (fun value => (profile value).getD [])
  have absent : choose markers values ∉ names := by
    intro member
    exact Nat.lt_irrefl _ (freeBound_lt names (freeBound names) member)
  refine ⟨InternedNestedProvenance.ordinary_available reader _, ?_, ?_⟩
  · intro member
    exact absent (List.mem_append_left _ member)
  · intro value included member
    exact absent (List.mem_append_right _ (List.mem_flatMap.mpr ⟨value,included,member⟩))

/-- One marker is fresh for both resolved body-leaf collections and the tracked names. -/
theorem bodies (markers : List Reference) (first second : Value Symbol Guard)
    (firstEnvironment secondEnvironment : Environment Symbol Guard) (reader : State Symbol Guard) :
    let marker := choose markers ((leaves first).map (input firstEnvironment) ++
      (leaves second).map (input secondEnvironment))
    Available reader (.reference marker) ∧ marker ∉ markers ∧
    (∀ leaf ∈ leaves first, marker ∉ (profile (input firstEnvironment leaf)).getD []) ∧
    (∀ leaf ∈ leaves second, marker ∉ (profile (input secondEnvironment leaf)).getD []) := by
  obtain ⟨available,untracked,absent⟩ := fresh markers
    ((leaves first).map (input firstEnvironment) ++ (leaves second).map (input secondEnvironment)) reader
  refine ⟨available,untracked,?_,?_⟩
  · intro leaf member
    exact absent _ (List.mem_append_left _ (List.mem_map.mpr ⟨leaf,member,rfl⟩))
  · intro leaf member
    exact absent _ (List.mem_append_right _ (List.mem_map.mpr ⟨leaf,member,rfl⟩))

end MicroCFTA.SourceCurrentTrackedMarkerChoice
