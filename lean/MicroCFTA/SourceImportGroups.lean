import MicroCFTA.ImportObservations
import MicroCFTA.DistinctRank
import MicroCFTA.SourceSizedBoundedSampling

/-!
# Finite members of imported observation parts

The graph splitter constructs the keys. Sorting changes only their order.
Each part filters a deduplicated finite language by its concrete observation
key. Coverage, disjointness, and counts follow from this construction.
The finite-language premise is the boundary to the fromTerms rebuild.
-/

namespace MicroCFTA.SourceImportGroups

open Language Observation ObservationGraph ImportObservations

/-- Sort actual split parts with the source observation comparison. -/
def parts [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (before : Variant State Symbol Refinement → Variant State Symbol Refinement → Bool) :=
  (ImportObservations.split A requested root).mergeSort before

/-- Sorting retains the actual graph variants and their constraints. -/
theorem parts_perm [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State) (before) :
    (parts A requested root before).Perm (ImportObservations.split A requested root) :=
  List.mergeSort_perm _ _

/-- One finite part keeps every distinct term with its exact requested observations. -/
def members [DecidableEq Symbol] [DecidableEq Refinement]
    (input : List (Term (Label Symbol Refinement))) (requested : List Path)
    (part : Variant State Symbol Refinement) : List (Term (Label Symbol Refinement)) :=
  input.eraseDups.filter fun term => decide
    (ImportObservations.key requested part.view = ImportObservations.key requested (requestedView requested term))

/-- The finite part predicate retains full labels, leafness, and absent paths. -/
theorem mem_members [DecidableEq Symbol] [DecidableEq Refinement]
    (input : List (Term (Label Symbol Refinement))) (requested : List Path)
    (part : Variant State Symbol Refinement) (term) :
    term ∈ members input requested part ↔ term ∈ input ∧
      ImportObservations.key requested part.view = ImportObservations.key requested (requestedView requested term) := by
  simp [members]

/-- A finite part has one occurrence per term even if its input contains repeats. -/
theorem members_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (input : List (Term (Label Symbol Refinement))) (requested : List Path) (part : Variant State Symbol Refinement) :
    (members input requested part).Nodup :=
  (SymbolicDriver.eraseDups_nodup input).filter _

/-- A duplicate-free key image identifies its original list member uniquely. -/
theorem key_injective (key : α → β) (items : List α) (unique : (items.map key).Nodup)
    (left right : α) (first : left ∈ items) (second : right ∈ items) (same : key left = key right) : left = right := by
  obtain ⟨i, hi, leftEq⟩ := List.mem_iff_getElem.mp first
  obtain ⟨j, hj, rightEq⟩ := List.mem_iff_getElem.mp second
  have positions : i = j := unique.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    (by simpa [leftEq, rightEq] using same)
  subst j
  exact leftEq.symm.trans rightEq

/-- A concrete graph variant accepts exactly its key's full source language. -/
theorem part_accepts [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (part : Variant State Symbol Refinement) (present : part ∈ ImportObservations.split A requested root) (term) :
    AcceptsNode A part.node term ↔ Accepts A root term ∧
      ImportObservations.key requested part.view = ImportObservations.key requested (requestedView requested term) := by
  constructor
  · intro accepted
    exact (group_language_exact A requested root _ term).mp ⟨part, present, rfl, accepted⟩
  · intro accepted
    obtain ⟨other, found, same, accepted⟩ := (group_language_exact A requested root _ term).mpr accepted
    have equal := key_injective (fun part => ImportObservations.key requested part.view)
      (ImportObservations.split A requested root) (split_keys_nodup A requested root) other part found present same
    simpa only [equal] using accepted

/-- A finite rebuilt language supplies every concrete part's members without a local decoder premise. -/
theorem members_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (input : List (Term (Label Symbol Refinement)))
    (language : ∀ term, Accepts A root term ↔ term ∈ input)
    (part : Variant State Symbol Refinement) (present : part ∈ ImportObservations.split A requested root) (term) :
    term ∈ members input requested part ↔ AcceptsNode A part.node term := by
  rw [mem_members, part_accepts A requested root part present, language]

/-- Every concrete part now has a constructed distinct-term index. -/
def partIndex [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (input : List (Term (Label Symbol Refinement)))
    (language : ∀ term, Accepts A root term ↔ term ∈ input)
    (part : Variant State Symbol Refinement) (present : part ∈ ImportObservations.split A requested root) :
    DistinctRank.Index (AcceptsNode A part.node) :=
  ⟨members input requested part, members_nodup input requested part,
    members_exact A requested root input language part present⟩

/-- Read each sorted graph part's finite members in its retained local order. -/
def groups [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (before : Variant State Symbol Refinement → Variant State Symbol Refinement → Bool)
    (input : List (Term (Label Symbol Refinement))) : List (List (Term (Label Symbol Refinement))) :=
  (parts A requested root before).map (members input requested)

/-- No term can occur in two emitted parts because their actual keys are distinct. -/
theorem groups_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State) (before)
    (input : List (Term (Label Symbol Refinement))) : (groups A requested root before input).flatten.Nodup := by
  change ((parts A requested root before).flatMap (members input requested)).Pairwise (· ≠ ·)
  apply List.pairwise_flatMap.mpr
  refine ⟨fun _ _ => members_nodup input requested _, ?_⟩
  have unique := reordered_keys_nodup A requested root (parts A requested root before) (parts_perm A requested root before)
  have different := List.pairwise_map.mp unique
  apply different.imp
  intro first second distinct left leftMem right rightMem same
  have firstKey := (mem_members input requested first left).mp leftMem |>.2
  have secondKey := (mem_members input requested second right).mp rightMem |>.2
  exact distinct (firstKey.trans (same ▸ secondKey.symm))

/-- The actual graph split preserves each finite source term exactly once. -/
theorem groups_perm [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State) (before)
    (input : List (Term (Label Symbol Refinement)))
    (language : ∀ term, Accepts A root term ↔ term ∈ input) :
    (groups A requested root before input).flatten.Perm input.eraseDups := by
  apply (List.perm_ext_iff_of_nodup (groups_nodup A requested root before input)
    (SymbolicDriver.eraseDups_nodup input)).mpr
  intro term
  simp only [groups, List.mem_flatten, List.mem_map, List.mem_eraseDups]
  constructor
  · rintro ⟨_, ⟨part, _, rfl⟩, member⟩
    exact ((mem_members input requested part term).mp member).1
  · intro member
    obtain ⟨part, present, accepted⟩ := (split_cover A requested root term).mpr ((language term).mpr member)
    exact ⟨members input requested part,
      ⟨part, (parts_perm A requested root before).mem_iff.mpr present, rfl⟩,
      (members_exact A requested root input language part present term).mpr accepted⟩

/-- Source cardinality weights sum to the number of distinct fallback terms. -/
theorem groups_count [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State) (before)
    (input : List (Term (Label Symbol Refinement)))
    (language : ∀ term, Accepts A root term ↔ term ∈ input) :
    ((groups A requested root before input).map List.length).sum = input.eraseDups.length := by
  rw [← List.length_flatten]
  exact (groups_perm A requested root before input language).length_eq

/-- Source live-cardinality filtering removes empty parts without changing ranks or counts. -/
def live [DecidableEq α] (groups : List (List α)) : List (List α) := groups.filter (fun group => group ≠ [])

theorem live_flatten [DecidableEq α] (groups : List (List α)) : (live groups).flatten = groups.flatten :=
  List.flatten_filter_ne_nil

/-- The grouped global index contains the entire rebuilt language exactly once. -/
def globalIndex [DecidableEq Symbol] [DecidableEq Refinement]
    (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
    (before : Variant State Symbol Refinement → Variant State Symbol Refinement → Bool)
    (input : List (Term (Label Symbol Refinement)))
    (language : ∀ term, Accepts A root term ↔ term ∈ input) : DistinctRank.Index (Accepts A root) where
  members := (groups A requested root before input).flatten
  nodup := groups_nodup A requested root before input
  exact := fun term => (groups_perm A requested root before input language).mem_iff.trans
    ((List.mem_eraseDups (a := term)).trans (language term).symm)

end MicroCFTA.SourceImportGroups
