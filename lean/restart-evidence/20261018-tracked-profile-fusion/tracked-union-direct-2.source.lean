import MicroCFTA.SourceCurrentTrackedFilteredFusion
import MicroCFTA.SourceCurrentSourceChildDepth
import MicroCFTA.SourceCurrentFilteredUnionCoverage
import MicroCFTA.SourceCurrentUsedBinderOutputTags

/-!
# Tracked root profiles through actual filtered source unions

Original member depths use the same bound as the parent. Two finite
preparations retain the historical source calls and warm reader calls.
Exact literal parts determine opacity and tracked root references.
-/
namespace MicroCFTA.SourceCurrentTrackedFilteredUnionFusion
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentTrackedFilteredFusion (Fusion)
open SourceCurrentTrackedRootProfile (mask observe Related)
open SourceCurrentLiteralRootParts (Literal Row)
open InternedRootProfile (Profile profile many combine Equivalent)
open InternedStoredMuOrigins (Normal)

private theorem many_nonopaque (markers : List Reference) (values : List (Value Symbol Guard)) :
    mask markers (many values) ≠ none ↔ ∀ value ∈ values, observe markers value ≠ none := by
  induction values with
  | nil => simp [many,mask]
  | cons first rest ih =>
      rw [many,SourceCurrentTrackedRootProfile.mask_combine]
      change combine (observe markers first) (mask markers (many rest)) ≠ none ↔ _
      cases one : observe markers first <;> cases two : mask markers (many rest) <;>
        simp_all [combine]

private theorem many_names (markers : List Reference) (values : List (Value Symbol Guard))
    (pure : mask markers (many values) ≠ none) (name : Reference) :
    name ∈ (mask markers (many values)).getD [] ↔
      ∃ value ∈ values, name ∈ (observe markers value).getD [] := by
  induction values with
  | nil => simp [many,mask]
  | cons first rest ih =>
      have members := (many_nonopaque markers (first::rest)).mp pure
      have one := members first List.mem_cons_self
      have tail := (many_nonopaque markers rest).mpr (fun value found => members value (List.mem_cons_of_mem _ found))
      have names := ih tail
      rw [many,SourceCurrentTrackedRootProfile.mask_combine]
      change combine (observe markers first) (mask markers (many rest)) ≠ none at pure
      change name ∈ (combine (observe markers first) (mask markers (many rest))).getD [] ↔ _
      cases firstProfile : observe markers first with
      | none => exact False.elim (one firstProfile)
      | some firstNames =>
          cases restProfile : mask markers (many rest) with
          | none => exact False.elim (tail restProfile)
          | some restNames =>
              change name ∈ (combine (some firstNames) (some restNames)).getD [] ↔ _
              simpa only [combine,Option.getD_some,List.mem_append,List.mem_cons,exists_eq_or_imp,firstProfile,
                Option.getD_some] using or_congr Iff.rfl names

private def PureParts (markers : List Reference) (value : Value Symbol Guard) : Prop :=
  (∀ row, ¬ Row value row) ∧ ∀ atom, Literal value atom → ∃ name, atom = .reference name ∧ name ∈ markers

private theorem nonopaque_parts (markers : List Reference) (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value) :
    observe markers value ≠ none ↔ PureParts markers value := by
  cases value with
  | empty =>
      constructor
      · intro _
        constructor
        · intro row found; cases found
        · intro atom found; cases found
      · intro _; simp [observe,profile,mask]
  | reference own =>
      have observed : observe markers (.reference own : Value Symbol Guard) ≠ none ↔ own ∈ markers := by
        simp [observe,profile,mask]
      rw [observed]
      constructor
      · intro tracked
        constructor
        · intro row found; cases found
        · intro atom found; cases found; exact ⟨own,rfl,tracked⟩
      · intro parts; obtain ⟨name,same,tracked⟩ := parts.2 _ (.reference own); cases same; exact tracked
  | mu entry body depth ordinary =>
      constructor
      · intro impossible; exact False.elim (impossible (by simp [observe,profile,mask]))
      · intro parts
        obtain ⟨name,impossible,_⟩ := parts.2 _ (.mu entry body depth ordinary)
        cases impossible
  | node entry rows level free =>
      constructor
      · intro impossible; exact False.elim (impossible (by simp [observe,profile,mask]))
      · intro parts
        have proper := InternedNonemptyRecords.resident_nonempty reader normal.proper _ available.resident
        obtain ⟨row,member⟩ := List.exists_mem_of_ne_nil rows proper
        exact False.elim (parts.1 row (.node member))
  | union entry members level free =>
      rw [observe,profile,many_nonopaque]
      constructor
      · intro pure
        constructor
        · intro row found
          obtain ⟨child,member,part⟩ := (SourceCurrentLiteralRootParts.row_union _ _ _ _ _).mp found
          exact ((nonopaque_parts markers reader normal child (available.children child member)).mp (pure child member)).1 row part
        · intro atom found
          obtain ⟨child,member,part⟩ := (SourceCurrentLiteralRootParts.literal_union _ _ _ _ _).mp found
          exact ((nonopaque_parts markers reader normal child (available.children child member)).mp (pure child member)).2 atom part
      · intro parts child member
        apply (nonopaque_parts markers reader normal child (available.children child member)).mpr
        exact ⟨fun row found => parts.1 row (.union member found),fun atom found => parts.2 atom (.union member found)⟩
termination_by sizeOf value
decreasing_by all_goals have smaller := List.sizeOf_lt_of_mem member; simp_wf; omega

private theorem reference_names (markers : List Reference) (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value)
    (pure : observe markers value ≠ none) (name : Reference) :
    name ∈ (observe markers value).getD [] ↔ Literal value (.reference name) := by
  cases value with
  | empty =>
      simp only [observe,profile,mask,List.all_nil,↓reduceIte,Option.getD_some,List.not_mem_nil,false_iff]
      intro impossible; cases impossible
  | reference own =>
      have tracked := (nonopaque_parts markers reader normal (.reference own) available).mp pure
      obtain ⟨other,same,present⟩ := tracked.2 _ (.reference own)
      cases same
      simp only [observe,profile,mask,List.all_cons,List.all_nil,Bool.and_true,List.contains_eq_mem,
        decide_eq_true_eq,present,↓reduceIte,Option.getD_some,List.mem_singleton]
      constructor
      · intro same; subst name; exact .reference _
      · intro found; cases found; rfl
  | node | mu => exact False.elim (pure (by simp [observe,profile,mask]))
  | union entry members level free =>
      have combined : mask markers (many members) ≠ none := by simpa only [observe,profile] using pure
      rw [observe,profile,many_names markers members combined]
      rw [SourceCurrentLiteralRootParts.literal_union]
      apply exists_congr
      intro child
      apply and_congr_right
      intro member
      exact reference_names markers reader normal child (available.children child member)
        ((many_nonopaque markers members).mp combined child member) name
termination_by sizeOf value
decreasing_by have smaller := List.sizeOf_lt_of_mem member; simp_wf; omega

end MicroCFTA.SourceCurrentTrackedFilteredUnionFusion
