import MicroCFTA.SourceImportGroups
import MicroCFTA.GroupedChoice
import MicroCFTA.SourcePmfQuery

/-!
# Count-weighted sampling of finite import groups

Finite observation groups use their constructed member counts as branch
weights. Empty groups contribute no branch. Uniform sampling inside each
group then assigns one equal share to every distinct imported term.
-/

namespace MicroCFTA.SourceImportGroupsSampling

open Language Observation ObservationGraph ImportObservations Probability
open SourceImportGroups SourceSizedBoundedSampling

/-- A finite part is empty or exposes its exact finite term inventory. -/
def alternative [DecidableEq α] (group : List α) : GroupedChoice.Alternative Unit (List α) :=
  ⟨false, if group = [] then .error .empty else .ok group⟩

/-- The source uniform worker weights live parts by their cardinalities. -/
def weighted [DecidableEq α] (groups : List (List α)) :=
  (live groups).map fun group => ((group.length : Rat), alternative group)

/-- Reading finite cardinalities derives every branch weight and removes empty parts. -/
theorem counted_alternatives [DecidableEq α] (groups : List (List α)) :
    GroupedChoice.counted List.length (groups.map alternative) = .ok (weighted groups) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      by_cases empty : group = []
      · simp [alternative, empty, GroupedChoice.counted, ih, weighted, live] at *
      · have positive : 0 < group.length := List.length_pos_iff.mpr empty
        simp [alternative, empty, GroupedChoice.counted, ih, weighted, live, positive] at *

/-- The finite alternatives contain no recursive dispatch marker. -/
theorem alternatives_finite [DecidableEq α] (groups : List (List α)) :
    (groups.map alternative).any GroupedChoice.Alternative.recursive = false := by
  simp [alternative]

/-- All constructed weighted parts are live, finite, and retain their member lists. -/
theorem weighted_live [DecidableEq α] (groups : List (List α)) :
    GroupedChoice.live (weighted groups) = (live groups).map (fun group => ((group.length : Rat), false, group)) := by
  have nonempty : ∀ group ∈ live groups, group ≠ [] := by simp [live]
  unfold weighted
  generalize live groups = retained at *
  induction retained with
  | nil => rfl
  | cons group rest ih =>
      simpa [GroupedChoice.live, alternative, nonempty group (by simp)] using
        ih (fun other member => nonempty other (by simp [member]))

/-- Constructed finite alternatives introduce no retained source failure. -/
theorem weighted_no_failure [DecidableEq α] (groups : List (List α)) :
    GroupedChoice.firstFailure (weighted groups) = none := by
  unfold weighted
  generalize live groups = retained
  induction retained with
  | nil => rfl
  | cons group rest ih =>
      by_cases empty : group = [] <;> simpa [GroupedChoice.firstFailure, alternative, empty] using ih

/-- Every retained cardinality supplies a strictly positive rational branch weight. -/
theorem weighted_positive [DecidableEq α] (groups : List (List α)) :
    (weighted groups).find? (fun entry => decide (entry.1 ≤ 0)) = none := by
  apply List.find?_eq_none.mpr
  intro entry member
  obtain ⟨group, present, rfl⟩ := List.mem_map.mp member
  have positive : 0 < group.length := List.length_pos_iff.mpr (by simpa [live] using (List.mem_filter.mp present).2)
  simp [Rat.not_le.mpr (Rat.natCast_pos.mpr positive)]

/-- The actual uniform finite dispatch derives its normalized shares from term counts. -/
theorem uniformly_exact [DecidableEq α] (groups : List (List α)) :
    GroupedChoice.uniformly List.length (groups.map alternative) =
      if live groups = [] then .error .empty else
        .ok (.finite (normalize ((live groups).map fun group => ((group.length : Rat), group)))) := by
  simp only [GroupedChoice.uniformly, alternatives_finite, Bool.false_eq_true, ↓reduceIte, counted_alternatives]
  simp only [GroupedChoice.frequencies, weighted_positive, weighted_no_failure, weighted_live]
  cases retained : live groups with
  | nil => rfl
  | cons group rest => simp [List.map_map, Function.comp_def]

/-- The source reports EmptyGenerator precisely when no group contains a member. -/
theorem live_empty_iff [DecidableEq α] (groups : List (List α)) : live groups = [] ↔ groups.flatten = [] := by
  constructor
  · intro empty
    rw [← live_flatten groups, empty]
    rfl
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro group member
    obtain ⟨present, nonempty⟩ := List.mem_filter.mp member
    have absent : group = [] := (List.flatten_eq_nil_iff.mp empty) group present
    simp [absent] at nonempty

/-- Cardinality-weighted uniform parts model the finite uniformlyGrouped member law. -/
def sampling [DecidableEq α] (groups : List (List α)) : Distribution α :=
  frequency (counted (live groups))

/-- Omitting empty parts preserves one equal share per retained member position. -/
theorem sampling_exact [DecidableEq α] (groups : List (List α)) :
    sampling groups = normalize (counting groups.flatten) := by
  rw [sampling, counted_exact, live_flatten]

variable [DecidableEq Symbol] [DecidableEq Refinement]
  (A : Automaton State (Label Symbol Refinement)) (requested : List Path) (root : State)
  (before : Variant State Symbol Refinement → Variant State Symbol Refinement → Bool)
  (input : List (Term (Label Symbol Refinement)))
  (language : ∀ term, Accepts A root term ↔ term ∈ input)

include language

/-- Grouping retains the uniform law of the distinct fallback language for every event. -/
theorem event_probability (event : Term (Label Symbol Refinement) → Bool) :
    eventMass event (sampling (groups A requested root before input)) =
      eventMass event (normalize (counting input.eraseDups)) := by
  rw [sampling_exact]
  exact normalized_perm_event event ((groups_perm A requested root before input language).map (fun term => (1, term)))

/-- The concrete member law is a probability distribution exactly when a fallback term exists. -/
theorem sampling_probability (nonempty : input ≠ []) :
    IsProbability (sampling (groups A requested root before input)) := by
  rw [sampling_exact]
  apply uniform_probability
  rw [(groups_perm A requested root before input language).length_eq]
  apply List.length_pos_iff.mpr
  intro empty
  cases input with
  | nil => exact nonempty rfl
  | cons first rest =>
      have member : first ∈ (first :: rest).eraseDups := List.mem_eraseDups.mpr (by simp)
      simp [empty] at member

/-- Every accepted term has the same reciprocal-count probability. -/
theorem uniform_term_probability (term : Term (Label Symbol Refinement)) (accepted : Accepts A root term) :
    eventMass (fun found => found == term) (sampling (groups A requested root before input)) =
      1 / (input.eraseDups.length : Rat) := by
  rw [event_probability A requested root before input language]
  exact (DistinctRank.Index.uniform_term_probability
    (⟨input.eraseDups, SymbolicDriver.eraseDups_nodup input,
      fun term => List.mem_eraseDups.trans (language term).symm⟩ : DistinctRank.Index (Accepts A root)) term accepted)

/-- Public output PMF aggregation preserves this same term law. -/
theorem pmf_event [Ord (Term (Label Symbol Refinement))] (event : Term (Label Symbol Refinement) → Bool) :
    eventMass event (SourcePmfAggregation.aggregate (sampling (groups A requested root before input))) =
      eventMass event (normalize (counting input.eraseDups)) := by
  rw [SourcePmfAggregation.event_aggregate]
  exact event_probability A requested root before input language event

/-- The source finite PMF query succeeds on each nonempty constructed import law. -/
theorem query_pmf [Ord (Term (Label Symbol Refinement))] (nonempty : input ≠ []) :
    SourcePmfQuery.finite (SourceError := Unit) (sampling (groups A requested root before input)) =
      .ok (SourcePmfAggregation.pmf (sampling (groups A requested root before input))) := by
  have totalOne := (sampling_probability A requested root before input language nonempty).2
  simp [SourcePmfQuery.finite, SourcePmfQuery.normalizeChecked, totalOne, normalize,
    scale_one, Except.map, show (0 : Rat) < 1 by decide]

/-- An observation class receives its cardinality divided by the complete distinct count. -/
theorem observation_probability (part : Variant State Symbol Refinement) :
    eventMass (fun term => decide (ImportObservations.key requested part.view =
      ImportObservations.key requested (requestedView requested term)))
      (sampling (groups A requested root before input)) =
        ((members input requested part).length : Rat) / (input.eraseDups.length : Rat) := by
  rw [event_probability A requested root before input language, uniform_event_probability]
  simp [members, List.countP_eq_length_filter]

/-- Distinct term decoding and encoding are inverse for the complete grouped language. -/
theorem rank_inverses :
    (∀ term, (globalIndex A requested root before input language).decode
      ((globalIndex A requested root before input language).encode term) = term) ∧
    (∀ rank, (globalIndex A requested root before input language).encode
      ((globalIndex A requested root before input language).decode rank) = rank) :=
  ⟨DistinctRank.Index.decode_encode _, DistinctRank.Index.encode_decode _⟩

/-- Grouped ranks cover precisely the number of distinct fallback terms. -/
theorem rank_count : (globalIndex A requested root before input language).count = input.eraseDups.length :=
  (groups_perm A requested root before input language).length_eq

end MicroCFTA.SourceImportGroupsSampling
