import MicroCFTA.InternedSourceFreeNames
import MicroCFTA.InternedProfileReferenceInputs

/-!
# Free names under arbitrary maps of literal source inputs

The source theorem compares actual completed executions. The name map
can identify captured references. The result concerns free-name sets;
canonical record identity and list order are separate properties.
-/
namespace MicroCFTA.InternedFreeNameTransport
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedNestedProvenance InternedStoredMuOrigins InternedRootProfile
open InternedProfileSemantics (mapNames)
open InternedProfileCallbackForm (captures)
open InternedBinderProtocol (Reference)

/-- A name map commutes with the symbolic free-name call and leaves its local marker unchanged. -/
theorem symbolic_map (function : Reference → Reference) (body : Syntax Symbol Guard)
    (profiles : List Profile) (freeNames : List (List Reference)) :
    InternedFreeNameForm.symbolic body (profiles.map (mapNames function)) (freeNames.map (List.map function)) =
      (InternedFreeNameForm.symbolic body profiles freeNames).map (Sum.map id function) := by
  unfold InternedFreeNameForm.symbolic
  rw [← InternedProfileSemantics.local_map function profiles,
    ← InternedFreeNameSemantics.local_map function freeNames,
    InternedFreeNameSemantics.evaluate_map]

/-- Actual mapped literal inputs have the same profile and free-name maps used by the pure theorem. -/
theorem literal_evaluate_map (function : Reference → Reference) (body : Syntax Symbol Guard)
    (names : List Reference) :
    InternedFreeNameSemantics.evaluate body
      ((names.map function).map (fun name => some [name])) ((names.map function).map (fun name => [name])) =
      (InternedFreeNameSemantics.evaluate body (names.map (fun name => some [name]))
        (names.map (fun name => [name]))).map function := by
  have result := InternedFreeNameSemantics.evaluate_map function body
    (names.map (fun name => some [name])) (names.map (fun name => [name]))
  simpa [List.map_map, Function.comp_def, mapNames] using result

/-- Mapped literal captures give exactly the mapped symbolic captured free names. -/
theorem literal_captures_map (function : Reference → Reference) (body : Syntax Symbol Guard)
    (names : List Reference) :
    captures (InternedFreeNameForm.symbolic body
      ((names.map function).map (fun name => some [name])) ((names.map function).map (fun name => [name]))) =
      (captures (InternedFreeNameForm.symbolic body (names.map (fun name => some [name]))
        (names.map (fun name => [name])))).map function := by
  have result := congrArg captures (symbolic_map function body
    (names.map (fun name => some [name])) (names.map (fun name => [name])))
  rw [InternedProfileReferenceInputs.captures_map] at result
  simpa [List.map_map, Function.comp_def, mapNames] using result

/-- Actual completed source evaluations transport free names through every literal-reference map. -/
theorem build_map [DecidableEq (EdgeKey Symbol Guard)] (function : Reference → Reference)
    (body : Syntax Symbol Guard) (names : List Reference)
    (before target : State Symbol Guard) (normal : Normal before) (targetNormal : Normal target)
    (inputs : Values before (names.map Value.reference))
    (targetInputs : Values target ((names.map function).map Value.reference))
    (heap : InternedFreeNameHeap.Heap before) (profiles : InternedProfileHeap.Heap before)
    (targetHeap : InternedFreeNameHeap.Heap target) (targetProfiles : InternedProfileHeap.Heap target)
    (first second : Value Symbol Guard) (after final : State Symbol Guard)
    (firstDone : build body (names.map Value.reference) before = .done first after)
    (secondDone : build body ((names.map function).map Value.reference) target = .done second final)
    (name : Reference) :
    name ∈ second.free ↔ ∃ original ∈ first.free, function original = name := by
  have left := (InternedNestedFreeNames.build_free body _ before normal inputs heap profiles).result first after firstDone
  have right := (InternedNestedFreeNames.build_free body _ target targetNormal targetInputs targetHeap targetProfiles).result second final secondDone
  simp only [List.map_map, Function.comp_def, profile, Value.free] at left right
  have mapped := literal_evaluate_map function body names
  simp only [List.map_map, Function.comp_def] at mapped
  rw [right name, mapped, List.mem_map]
  exact exists_congr fun original => and_congr (left original).symm Iff.rfl

/-- Normalized callbacks transport every name other than the target's supplied local, even when names merge. -/
theorem callback_map [DecidableEq (EdgeKey Symbol Guard)] (function : Reference → Reference)
    (body : Syntax Symbol Guard) (names : List Reference) (argument : Reference)
    (before target : State Symbol Guard) (normal : Normal before) (targetNormal : Normal target)
    (inputs : Values before (.reference argument :: names.map Value.reference))
    (targetInputs : Values target (.reference (function argument) :: (names.map function).map Value.reference))
    (heap : InternedFreeNameHeap.Heap before) (profiles : InternedProfileHeap.Heap before)
    (targetHeap : InternedFreeNameHeap.Heap target) (targetProfiles : InternedProfileHeap.Heap target)
    (first second : Value Symbol Guard) (after final : State Symbol Guard)
    (firstDone : callback body (names.map Value.reference) argument before = .done first after)
    (secondDone : callback body ((names.map function).map Value.reference) (function argument) target = .done second final)
    (name : Reference) (different : name ≠ function argument) :
    name ∈ second.free ↔ ∃ original ∈ first.free, function original = name := by
  have left := (InternedSourceFreeNames.callback_checked body _ argument before normal inputs heap profiles).result first after firstDone
  have right := (InternedSourceFreeNames.callback_checked body _ (function argument) target targetNormal targetInputs targetHeap targetProfiles).result second final secondDone
  simp only [List.map_map, Function.comp_def, profile, Value.free] at left right
  have mapped := literal_captures_map function body names
  simp only [List.map_map, Function.comp_def] at mapped
  rw [right name different, mapped, List.mem_map]
  constructor
  · rintro ⟨original, member, same⟩
    have other : original ≠ argument := by
      intro equal
      exact different (same.symm.trans (congrArg function equal))
    exact ⟨original, (left original other).mpr member, same⟩
  · rintro ⟨original, member, same⟩
    have other : original ≠ argument := by
      intro equal
      exact different (same.symm.trans (congrArg function equal))
    exact ⟨original, (left original other).mp member, same⟩

end MicroCFTA.InternedFreeNameTransport
