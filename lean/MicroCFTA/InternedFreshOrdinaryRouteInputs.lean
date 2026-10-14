import MicroCFTA.InternedFreshOrdinaryEarlierPair
import MicroCFTA.InternedFreshOrdinaryLiveInputSupport

/-!
# Mixed lexical inputs for actual repaired source routes

Paired varying slots retain the actual earlier and current reference names.
The ancestor's captured values form an unchanged fixed tail.
Every changed varying slot is ordinary or a sufficiently fresh interned name.
-/
namespace MicroCFTA.InternedFreshOrdinaryRouteInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryActiveSite InternedFreshOrdinaryLiveInputs
open InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)

/-- Paired lexical inputs retain the actual route and the active fresh local. -/
def routeAtoms [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) : List (Reference × Reference) :=
  (earlier.zip current).map (fun pair => (pair.1.name, pair.2.name)) ++
    [(.depth, .interned origin.entry.identity)]

/-- Vary the actual crossed references and retain the complete original captured values. -/
def routeInputs [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) : List (Sum (Value Symbol Guard) (Reference × Reference)) :=
  (routeAtoms origin earlier current).map Sum.inr ++ origin.environment.map Sum.inl

/-- Both mixed-input instantiations recover their exact actual lexical values. -/
theorem route_values [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) (lengths : earlier.length = current.length) :
    (routeInputs origin earlier current).map (input Prod.fst) =
      earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment ∧
    (routeInputs origin earlier current).map (input Prod.snd) =
      current.map (fun crossing => Value.reference crossing.name) ++ origin.localInputs := by
  have first := congrArg (List.map (fun crossing => Value.reference (Symbol := Symbol) (Guard := Guard) crossing.name))
    (List.map_fst_zip (Nat.le_of_eq lengths))
  have second := congrArg (List.map (fun crossing => Value.reference (Symbol := Symbol) (Guard := Guard) crossing.name))
    (List.map_snd_zip (Nat.le_of_eq lengths.symm))
  constructor
  · simpa [routeInputs, routeAtoms, input, List.map_map, Function.comp_def] using
      congrArg (fun values => values ++ .reference .depth :: origin.environment) first
  · simpa [routeInputs, routeAtoms, input, Origin.localInputs, List.map_map, Function.comp_def] using
      congrArg (fun values => values ++ .reference (.interned origin.entry.identity) :: origin.environment) second

/-- Each varying slot in the mixed route comes from its actual paired reference prefix. -/
theorem route_member [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) (atom : Reference × Reference)
    (member : .inr atom ∈ routeInputs origin earlier current) : atom ∈ routeAtoms origin earlier current := by
  simp only [routeInputs, List.mem_append, List.mem_map] at member
  rcases member with ⟨previous, included, same⟩ | ⟨value, _, impossible⟩
  · exact Sum.inr.inj same ▸ included
  · cases impossible

/-- A changed paired input is ordinary or fresh on the current route. -/
theorem routeAtoms_changed [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard))
    (descriptors : earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
      current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)))
    (fresh : ∀ crossing ∈ current, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity)
    (index : Nat) (atom : Reference × Reference) (member : (routeAtoms origin earlier current)[index]? = some atom)
    (different : atom.1 ≠ atom.2) :
    (∃ identity, origin.cut.nodes.next ≤ identity ∧ atom.2 = .interned identity) ∨
    ∃ (previous : InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
      earlier[index]? = some previous ∧ current[index]? = some actual ∧
      previous.body = actual.body ∧ previous.ordinary = true ∧ actual.name = .uninterned level ∧
      (ordinaryLevel previous.depth) ≠ level ∧ atom = (.uninterned (ordinaryLevel previous.depth), .uninterned level) := by
  by_cases front : index < (earlier.zip current).length
  · rw [routeAtoms, List.getElem?_append_left (by simpa using front), List.getElem?_map] at member
    obtain ⟨pair, atPair, same⟩ := Option.map_eq_some_iff.mp member
    have paired := List.mem_of_getElem? atPair
    have positions := List.getElem?_zip_eq_some.mp atPair
    have selected := congrArg (fun list => list[index]?) descriptors
    simp only [List.getElem?_map, positions.1, positions.2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
    rcases Crossing.name_cases pair.2 with named | ⟨level, named⟩ | ⟨identity, named⟩
    · have flag : pair.1.ordinary = false := by simpa only [Crossing.probeChoice, named] using selected.2
      have equal : atom.1 = atom.2 := by rw [← same]; simp [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, named]
      exact False.elim (different equal)
    · have flag : pair.1.ordinary = true := by simpa only [Crossing.probeChoice, named] using selected.2
      have atomSame : atom = (.uninterned (ordinaryLevel pair.1.depth), .uninterned level) := by
        rw [← same]; simp [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, named]
      refine Or.inr ⟨pair.1, pair.2, level, positions.1, positions.2, selected.1, flag, named, ?_, atomSame⟩
      intro equal
      apply different
      simp [atomSame, equal]
    · exact Or.inl ⟨identity, fresh pair.2 (List.of_mem_zip paired).2 identity named, by rw [← same]; exact named⟩
  · rw [routeAtoms, List.getElem?_append_right (by simpa using Nat.le_of_not_gt front)] at member
    have same := List.mem_singleton.mp (List.mem_of_getElem? member)
    exact Or.inl ⟨origin.entry.identity,
      Nat.le_of_eq (intern_miss_identity origin.cut.nodes key origin.missing).symm, by rw [same]⟩

end MicroCFTA.InternedFreshOrdinaryRouteInputs
