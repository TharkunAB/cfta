import MicroCFTA.FiniteSource

/-!
# Recursive automaton records and bounded sampling

The actual exact-size plan supplies the sampler's cardinality and decoder.
The default value is used only outside the decoder's valid range. The proofs
show that a sampled rank never reads it. Plain cyclic automata are compiled
by the checked decreasing-size recurrence, so exact-size correctness is derived.
-/

namespace MicroCFTA.RecursiveRecord
open Language Probability Sampler SamplerReplay

/-- Cached decoder sampling for a finite plan, including an empty class. -/
def uniformRecord (plan : Decoder.Plan α) (fallback : α) : Record α :=
  ⟨plan, uniformSampler (Decoder.count plan) (fun rank => (Decoder.decode plan rank).getD fallback)⟩

/-- A rank appearing in the exact uniform backend satisfies its strict bound. -/
theorem uniform_rank_bound (count : Nat) (entry : Rat × Nat) (present : entry ∈ uniformRanks count) :
    entry.2 < count := by
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨rank, rankMember, rfl⟩ := List.mem_map.mp member
  exact List.mem_range.mp rankMember

/-- Uniform sampling only observes successful decoder results. -/
theorem uniform_coherent (plan : Decoder.Plan α) (fallback : α) :
    SamplerReplay.Coherent (uniformRecord plan fallback) := by
  refine ⟨uniformSampler_coherent _ _, ?_⟩
  intro entry present
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  have bound := uniform_rank_bound _ original member
  obtain ⟨value, found⟩ := Decoder.decode_exists plan original.2 bound
  simp [uniformRecord, found]

/-- Every valid backend rank occurs with strictly positive uniform mass. -/
theorem uniform_rank_member (count rank : Nat) (within : rank < count) :
    ∃ mass, 0 < mass ∧ (mass, rank) ∈ uniformRanks count := by
  have positive : (0 : Rat) < count := Rat.natCast_pos.mpr (by omega)
  refine ⟨(count : Rat)⁻¹, Rat.inv_pos.mpr positive, ?_⟩
  change _ ∈ scale (total (counting (List.range count)))⁻¹ (counting (List.range count))
  rw [total_counting, List.length_range]
  apply List.mem_map.mpr
  refine ⟨(1, rank), List.mem_map.mpr ⟨rank, List.mem_range.mpr within, rfl⟩, ?_⟩
  simp

/-- Decoder-based uniform sampling covers every valid replay position. -/
theorem uniform_covers (plan : Decoder.Plan α) (fallback : α) : Covers (uniformRecord plan fallback) := by
  intro rank within
  obtain ⟨value, found⟩ := Decoder.decode_exists plan rank within
  obtain ⟨mass, positive, member⟩ := uniform_rank_member _ rank within
  refine ⟨mass, value, positive, ?_, found⟩
  exact List.mem_map.mpr ⟨(mass, rank), member, by simp [found]⟩

/-- The source's cached-decoder uniform path satisfies the complete finite record invariant. -/
theorem uniform_live (plan : Decoder.Plan α) (fallback : α) : LiveValid (uniformRecord plan fallback) :=
  ⟨uniform_coherent plan fallback, uniform_covers plan fallback,
    fun positive => uniformSampler_probability _ _ positive⟩

/-- Applying the decoder to every valid rank returns the complete member list in order. -/
theorem decode_range (plan : Decoder.Plan α) (fallback : α) :
    (List.range (Decoder.count plan)).map (fun rank => (Decoder.decode plan rank).getD fallback) =
      Decoder.values plan := by
  apply List.ext_getElem
  · simp [Decoder.count_correct]
  · intro rank leftBound rightBound
    simp [Decoder.decode_correct, List.getElem?_eq_getElem rightBound]

/-- The cached decoder's exact sampler is uniform over member positions, including duplicate values. -/
theorem uniform_values (plan : Decoder.Plan α) (fallback : α) :
    (uniformRecord plan fallback).sampling.values = normalize (counting (Decoder.values plan)) := by
  unfold uniformRecord uniformSampler uniformRanks
  rw [map_normalize, map_counting, decode_range]

/-- Compile a complete exact-size automaton class and use its cached decoder for sampling. -/
def classRecord (automaton : Automaton State Symbol) (state : State) (size : Nat) (fallback : Term Symbol) :
    Record (Term Symbol) := uniformRecord (Decoder.normalize (RecursiveSize.compileAt automaton size state)) fallback

/-- The recursive class count is the same checked recurrence used by its sampler and decoder. -/
theorem class_count (automaton : Automaton State Symbol) (state : State) (size : Nat) (fallback : Term Symbol) :
    Decoder.count (classRecord automaton state size fallback).plan = RecursiveSize.countAt automaton size state := by
  simp [classRecord, uniformRecord, Decoder.count_normalize, RecursiveSize.count_compileAt]

/-- Every recursive class has a valid decoder/sampler record without an assumed class law. -/
theorem class_live (automaton : Automaton State Symbol) (state : State) (size : Nat) (fallback : Term Symbol) :
    LiveValid (classRecord automaton state size fallback) := uniform_live _ _

/-- Exact-size samples are all and only the accepted complete terms in that class. -/
theorem class_sample_exact (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (size : Nat) (fallback term : Term Symbol) :
    (∃ rank mass, 0 < mass ∧ (mass, (rank, term)) ∈ (classRecord automaton state size fallback).sampling.ranked) ↔
      Accepts automaton state term ∧ RecursiveSize.nodeSize term = size := by
  have valid := class_live automaton state size fallback
  rw [← RecursiveSize.compiled_coverage automaton plain size state term]
  constructor
  · rintro ⟨rank, mass, _, member⟩
    have decoded := valid.1.2 _ member
    refine ⟨rank, ?_, decoded⟩
    rw [← class_count automaton state size fallback]
    exact decoded_bound _ _ _ decoded
  · rintro ⟨rank, within, decoded⟩
    rw [← class_count automaton state size fallback] at within
    obtain ⟨mass, value, positive, member, found⟩ := valid.2.1 rank within
    have same : value = term := Option.some.inj (found.symm.trans decoded)
    subst value
    exact ⟨rank, mass, positive, member⟩

/-- Bound the actual recursive class records with the source's count-weighted size sampler. -/
def bounded (automaton : Automaton State Symbol) (state : State) (bound : Nat) (fallback : Term Symbol) :
    Record (Term Symbol) := boundedRecord (fun size => classRecord automaton state size fallback) bound

/-- All bounded class record fields agree, and every valid rank has positive probability. -/
theorem bounded_live (automaton : Automaton State Symbol) (state : State) (bound : Nat) (fallback : Term Symbol) :
    LiveValid (bounded automaton state bound fallback) := SamplerReplay.bounded_live _ _ (fun size => class_live _ _ size _)

/-- The bounded record's structural members are exactly the checked bounded run enumeration. -/
theorem bounded_values (automaton : Automaton State Symbol) (state : State) (bound : Nat) (fallback : Term Symbol) :
    Decoder.values (bounded automaton state bound fallback).plan = RecursiveSize.enumerateAtMost automaton bound state := by
  simp [bounded, boundedRecord, manyRecord, manyPlan_values, List.flatMap_map, classRecord, uniformRecord,
    Decoder.values_normalize, RecursiveSize.values_compileAt, RecursiveSize.enumerateAtMost]

/-- The complete recursive compile/bound/sample path inserts and drops no accepted bounded term. -/
theorem bounded_sample_exact (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (bound : Nat) (fallback term : Term Symbol) :
    (∃ rank mass, 0 < mass ∧ (mass, (rank, term)) ∈ (bounded automaton state bound fallback).sampling.ranked) ↔
      Accepts automaton state term ∧ RecursiveSize.nodeSize term ≤ bound := by
  have valid := bounded_live automaton state bound fallback
  rw [← RecursiveSize.mem_enumerateAtMost_iff automaton plain bound state term,
    ← bounded_values automaton state bound fallback, Decoder.mem_values_iff]
  constructor
  · rintro ⟨rank, mass, _, member⟩
    have decoded := valid.1.2 _ member
    exact ⟨rank, decoded_bound _ _ _ decoded, decoded⟩
  · rintro ⟨rank, within, decoded⟩
    obtain ⟨mass, value, positive, member, found⟩ := valid.2.1 rank within
    have same : value = term := Option.some.inj (found.symm.trans decoded)
    subst value
    exact ⟨rank, mass, positive, member⟩

/-- Retain the nonempty classes with their structural count as branch mass. -/
def countingParts (classes : List (List α)) : List (Rat × Distribution α) :=
  classes.filterMap fun values => if 0 < values.length then
    some ((values.length : Rat), normalize (counting values)) else none

/-- Class count factors cancel their uniform normalization and retain every member occurrence. -/
theorem counting_parts_exact (classes : List (List α)) :
    branchWeight (countingParts classes) = (classes.flatten.length : Rat) ∧
      mix (countingParts classes) = counting classes.flatten := by
  induction classes with
  | nil => simp [countingParts, branchWeight, mix, counting]
  | cons first rest ih =>
      by_cases nonempty : 0 < first.length
      · simp only [countingParts, List.filterMap_cons, ite_eq_left nonempty]
        change (first.length : Rat) + branchWeight (countingParts rest) = ((first ++ rest.flatten).length : Rat) ∧
          scale (first.length : Rat) (normalize (counting first)) ++ mix (countingParts rest) = counting (first ++ rest.flatten)
        constructor
        · rw [ih.1]
          simp
        · have positive : (0 : Rat) < first.length := Rat.natCast_pos.mpr nonempty
          have nonzero : total (counting first) ≠ 0 := by rw [total_counting]; exact Rat.ne_of_gt positive
          rw [← total_counting first, restore_normalized _ nonzero, ih.2]
          simp [counting]
      · have empty : first = [] := List.length_eq_zero_iff.mp (by omega)
        subst first
        simpa [countingParts] using ih

/-- Count-weighted uniform classes are uniform over the full flattened replay range. -/
theorem weighted_counting (classes : List (List α)) :
    weightedChoice (classes.map fun values => (values.length, (values.length : Rat), normalize (counting values))) =
      normalize (counting classes.flatten) := by
  have same : (classes.map fun values => (values.length, (values.length : Rat), normalize (counting values))).filterMap
      (fun (count, mass, outcomes) => if 0 < count ∧ 0 < mass then some (mass, outcomes) else none) = countingParts classes := by
    simp [List.filterMap_map, Function.comp_def, Rat.natCast_pos, countingParts]
  rw [weightedChoice, same, frequency, (counting_parts_exact classes).1, (counting_parts_exact classes).2,
    normalize, total_counting]

/-- Recursive class probability is uniform over the exact compiled run list. -/
theorem class_distribution (automaton : Automaton State Symbol) (state : State) (size : Nat) (fallback : Term Symbol) :
    (classRecord automaton state size fallback).sampling.values =
      normalize (counting (RecursiveSize.enumerate automaton size state)) := by
  rw [classRecord, uniform_values, Decoder.values_normalize, RecursiveSize.values_compileAt]

/-- The actual class sampler and its size-count weighting equal uniform bounded run sampling. -/
theorem bounded_distribution (automaton : Automaton State Symbol) (state : State) (bound : Nat) (fallback : Term Symbol) :
    (bounded automaton state bound fallback).sampling.values =
      normalize (counting (RecursiveSize.enumerateAtMost automaton bound state)) := by
  simp only [bounded, boundedRecord, many_values, List.map_map, Function.comp_def,
    class_count, RecursiveSize.countAt_correct, class_distribution]
  have exactClasses := weighted_counting ((List.range (bound + 1)).map (fun size => RecursiveSize.enumerate automaton size state))
  simpa [List.map_map, Function.comp_def, List.flatMap_def, RecursiveSize.enumerateAtMost] using exactClasses

/-- Every event receives exactly its number of bounded run ranks divided by the derived total count. -/
theorem bounded_event_probability (automaton : Automaton State Symbol) (state : State) (bound : Nat)
    (fallback : Term Symbol) (event : Term Symbol → Bool) :
    eventMass event (bounded automaton state bound fallback).sampling.values =
      ((RecursiveSize.enumerateAtMost automaton bound state).countP event : Rat) /
        RecursiveSize.countAtMost automaton bound state := by
  rw [bounded_distribution, uniform_event_probability, RecursiveSize.countAtMost_correct]

end MicroCFTA.RecursiveRecord
