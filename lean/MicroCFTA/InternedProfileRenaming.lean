import MicroCFTA.InternedProfileComposition

/-!
# Empty and direct-local observations under name maps

External names can merge under a map. The empty observation is unchanged.
The direct-local observation is unchanged when the target local has only
the selected source local as its preimage. Source root normalization
preserves both observations.
-/
namespace MicroCFTA.InternedProfileRenaming
open InternedRootProfile InternedProfileSemantics InternedTwoProbeProfiles
open InternedNestedConstruction
open InternedBinderProtocol (Reference)

/-- Every external-name map preserves the pure empty case. -/
theorem mapped_empty (function : Reference → Reference) (value : Profile) :
    mapNames function value = some [] ↔ value = some [] := by
  cases value with
  | none => simp [mapNames]
  | some names => simp [mapNames]

/-- Mapping root names reflects the selected local when it has one possible preimage. -/
theorem mapped_single (function : Reference → Reference) (first second : Reference)
    (localName : ∀ name, function name = second ↔ name = first) (value : Profile) :
    Single second ((mapNames function value).getD []) ↔ Single first (value.getD []) := by
  cases value with
  | none => simp [mapNames, Single]
  | some names =>
      simp only [mapNames, Option.map_some, Option.getD_some]
      constructor
      · rintro ⟨present, only⟩
        obtain ⟨name, member, same⟩ := List.mem_map.mp present
        have selected := (localName name).mp same
        refine ⟨selected ▸ member, ?_⟩
        intro other included
        exact (localName other).mp (only _ (List.mem_map.mpr ⟨other, included, rfl⟩))
      · rintro ⟨present, only⟩
        refine ⟨List.mem_map.mpr ⟨first, present, (localName first).mpr rfl⟩, ?_⟩
        intro other included
        obtain ⟨name, member, rfl⟩ := List.mem_map.mp included
        exact (localName name).mpr (only name member)

/-- Actual root-profile normalization preserves the pure empty case. -/
theorem normalized_empty (name : Reference) (value : Profile) :
    normalize name value = some [] ↔ value = some [] := by
  cases value with
  | none => simp [normalize]
  | some names => simpa only [Option.some.injEq] using normalize_empty name names

/-- Actual root-profile normalization preserves the direct-local case. -/
theorem normalized_single (name : Reference) (value : Profile) :
    Single name ((normalize name value).getD []) ↔ Single name (value.getD []) := by
  cases value with
  | none => simp [normalize, Single]
  | some names => exact normalize_single name names

/-- Different normalized local names retain empty and direct-local observations under the same source name map. -/
theorem normalized_reflections (function : Reference → Reference) (first second : Reference)
    (localName : ∀ name, function name = second ↔ name = first) (value : Profile) :
    (normalize first value = some [] ↔ normalize second (mapNames function value) = some []) ∧
      (Single first ((normalize first value).getD []) ↔
        Single second ((normalize second (mapNames function value)).getD [])) := by
  constructor
  · rw [normalized_empty, normalized_empty, mapped_empty]
  · rw [normalized_single, normalized_single, mapped_single function first second localName]

/-- Equivalent profiles preserve the direct-local observation without inspecting list multiplicities. -/
theorem single_equivalent (name : Reference) {first second : Profile} (same : Equivalent first second) :
    Single name (first.getD []) ↔ Single name (second.getD []) := by
  constructor
  · rintro ⟨present, only⟩
    exact ⟨(same.2 name).mp present, fun other member => only other ((same.2 other).mpr member)⟩
  · rintro ⟨present, only⟩
    exact ⟨(same.2 name).mpr present, fun other member => only other ((same.2 other).mp member)⟩

/-- Full body interpretation follows a map on the local reference and every captured profile. -/
theorem body_mapped (expression : Syntax Symbol Guard) (function : Reference → Reference)
    (first second : Reference) (sameLocal : function first = second)
    (left right : List Profile) (sameInputs : right = left.map (mapNames function)) :
    evaluate expression (some [second] :: right) =
      mapNames function (evaluate expression (some [first] :: left)) := by
  rw [← evaluate_map function expression]
  congr 1
  simp [sameInputs, mapNames, sameLocal]

end MicroCFTA.InternedProfileRenaming
