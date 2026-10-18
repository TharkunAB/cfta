import MicroCFTA.SourceCurrentSourceEmptyAbstraction
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedFreshOrdinaryDependencies

/-!
# Physical Empty congruence on original stored free names

The same stored value can use different available replacement records.
Only their resolved physical Empty tests must agree on its original free
names. Internal bound names are removed from both external maps before the
fixed full source plan is compared. Entry and return heaps can differ.
-/
namespace MicroCFTA.SourceCurrentStoredEmptyCongruence
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute execute_restrict)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference)

/-- Resolved Empty agreement on original free names preserves actual repaired output Empty tests. -/
theorem execute_same [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (first second : Environment Symbol Guard)
    (before later : State Symbol Guard) (firstReady : Ready before) (secondReady : Ready later)
    (firstAvailable : Available before value) (secondAvailable : Available later value)
    (firstReplacements : Replacements before first) (secondReplacements : Replacements later second)
    (left : Value Symbol Guard) (after : State Symbol Guard)
    (right : Value Symbol Guard) (final : State Symbol Guard)
    (firstDone : execute value first before = .done left after)
    (secondDone : execute value second later = .done right final)
    (agree : ∀ name ∈ value.free,
      (((first name).getD (.reference name)).referenceOf == .empty) =
        (((second name).getD (.reference name)).referenceOf == .empty)) :
    (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  let restrictedFirst : Environment Symbol Guard := fun name => if name ∈ value.free then first name else none
  let restrictedSecond : Environment Symbol Guard := fun name => if name ∈ value.free then second name else none
  have firstRestricted : Replacements before restrictedFirst := by
    intro name replacement found
    dsimp only [restrictedFirst] at found
    split at found
    · exact firstReplacements name replacement found
    · cases found
  have secondRestricted : Replacements later restrictedSecond := by
    intro name replacement found
    dsimp only [restrictedSecond] at found
    split at found
    · exact secondReplacements name replacement found
    · cases found
  let firstInputs := (leaves value).map (input restrictedFirst)
  let secondInputs := (leaves value).map (input restrictedSecond)
  let plan := encode (leaves value) [] value
  have firstContext : InternedFreshOrdinaryContext.Context before firstInputs :=
    ⟨firstReady.semantic.1.normal,inputs_available value restrictedFirst before firstAvailable firstRestricted,
      firstReady.semantic.1.profiles,firstReady.semantic.1.freeNames⟩
  have secondContext : InternedFreshOrdinaryContext.Context later secondInputs :=
    ⟨secondReady.semantic.1.normal,inputs_available value restrictedSecond later secondAvailable secondRestricted,
      secondReady.semantic.1.profiles,secondReady.semantic.1.freeNames⟩
  have firstActual : build plan firstInputs before = .done left after :=
    (execute_restrict value first before firstReady.semantic.1.normal.facts.coherent firstAvailable).trans firstDone
  have secondActual : build plan secondInputs later = .done right final :=
    (execute_restrict value second later secondReady.semantic.1.normal.facts.coherent secondAvailable).trans secondDone
  have flags : firstInputs.map (fun leaf => leaf.referenceOf == .empty) =
      secondInputs.map (fun leaf => leaf.referenceOf == .empty) := by
    dsimp only [firstInputs,secondInputs]
    rw [List.map_map,List.map_map]
    apply List.map_congr_left
    intro leaf _
    cases leaf with
    | reference name =>
        by_cases member : name ∈ value.free
        · simpa only [input,restrictedFirst,restrictedSecond,if_pos member] using agree name member
        · simp only [input,restrictedFirst,restrictedSecond,if_neg member,Option.getD_none]
    | empty | node | union | mu => rfl
  exact SourceCurrentSourceEmptyAbstraction.source plan firstInputs secondInputs before after later final
    firstContext secondContext left right firstActual secondActual flags

end MicroCFTA.SourceCurrentStoredEmptyCongruence
