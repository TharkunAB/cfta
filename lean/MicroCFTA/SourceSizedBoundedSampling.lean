import MicroCFTA.SourceSizedSampling

/-!
# Count-weighted sampling of finite size prefixes

The source bounded sampler chooses a size class by its cardinality. It then
uses the sampler for that class. Uniform distinct class samplers therefore
give a uniform distribution on the complete distinct prefix. Empty classes
contribute no outcomes and do not stop the prefix.
-/

namespace MicroCFTA.SourceSizedBoundedSampling

open Language RecursiveSize Probability SourceSizedDecided SourceSizedDispatcher
open SourceSizedPreprocessing SourceGuards SourceObservations SourceSymbolicIndex

/-- Class cardinalities are the outer weights of uniform class distributions. -/
def counted (groups : List (List α)) : List (Rat × Distribution α) :=
  groups.map fun group => ((group.length : Rat), normalize (counting group))

/-- Restoring the count also works for an empty uniform class. -/
theorem restore_counting (group : List α) :
    scale (group.length : Rat) (normalize (counting group)) = counting group := by
  cases group with
  | nil => rfl
  | cons value rest =>
      rw [← total_counting]
      apply restore_normalized
      rw [total_counting]
      exact Rat.ne_of_gt (Rat.natCast_pos.mpr (by simp))

/-- Mixing classes at their counts restores one unit of mass per listed term. -/
theorem counted_mix (groups : List (List α)) :
    mix (counted groups) = counting groups.flatten := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change scale (group.length : Rat) (normalize (counting group)) ++ mix (counted rest) = _
      rw [restore_counting, ih]
      simp [counting]

/-- The sum of class counts is the length of the concatenated prefix. -/
theorem counted_weight (groups : List (List α)) :
    branchWeight (counted groups) = (groups.flatten.length : Rat) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change (group.length : Rat) + branchWeight (counted rest) = _
      rw [ih]
      simp

/-- Count-weighted uniform classes equal one uniform distribution on the prefix. -/
theorem counted_exact (groups : List (List α)) :
    frequency (counted groups) = normalize (counting groups.flatten) := by
  rw [frequency, counted_mix, counted_weight, normalize, total_counting]

/-- The source live-class worker retains each class count and its value sampler. -/
theorem bounded_parts (classes : List (Nat × Nat)) (sampling : Sampler.SampleIndex α)
    (positive : ∀ entry ∈ classes, 0 < entry.2) (offset : Nat) :
    (Sampler.choiceParts offset (classes.map (fun entry =>
      ⟨entry.2, (entry.2 : Rat), sampling entry.1⟩))).map
        (fun part => (part.mass, part.sampling.values)) =
      classes.map (fun entry => ((entry.2 : Rat), (sampling entry.1).values)) := by
  induction classes generalizing offset with
  | nil => rfl
  | cons entry rest ih =>
      have head := positive entry (by simp)
      have tail := fun item member => positive item (List.mem_cons_of_mem entry member)
      simp [Sampler.choiceParts, head, Rat.natCast_pos.mpr head, ih tail]

/-- The bounded source sampler uses the specified uniform class distributions. -/
theorem bounded_exact (classes : Nat → List α) (sizes : List Nat)
    (sampling : Sampler.SampleIndex α)
    (positive : ∀ size ∈ sizes, 0 < (classes size).length)
    (uniform : ∀ size ∈ sizes, (sampling size).values = normalize (counting (classes size))) :
    (Sampler.boundedSampler (sizes.map (fun size => (size, (classes size).length))) sampling).values =
      normalize (counting (sizes.flatMap classes)) := by
  unfold Sampler.boundedSampler Sampler.chooseSampler
  rw [bounded_parts]
  · have branches :
        ((sizes.map (fun size => (size, (classes size).length))).map
          (fun entry => ((entry.2 : Rat), (sampling entry.1).values))) =
        counted (sizes.map classes) := by
      simp only [counted, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro size member
      rw [uniform size member]
    rw [branches, counted_exact]
    rfl
  · intro entry member
    obtain ⟨size, present, rfl⟩ := List.mem_map.mp member
    exact positive size present

/-- Query clients can mix all classes through a bound, including empty classes. -/
def publicPrefix (api : Api Symbol) (bound : Nat) : Distribution (Term Symbol) :=
  frequency (counted ((List.range (bound + 1)).map (fun size : Nat => api.terms size)))

/-- The class mixture is the exact uniform distribution on the public size-major prefix. -/
theorem publicPrefix_exact (api : Api Symbol) (bound : Nat) :
    publicPrefix api bound = normalize
      (counting (SourceSizedQueries.through (fun size : Nat => api.terms size) bound)) := by
  rw [publicPrefix, counted_exact]
  rfl

variable [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
  (input : Input State (Label Formula) (Constraint Formula))
  (api : Api (Label Formula)) (success : publicSized input = .ok api)

include success

/-- Every distinct public prefix term gets the reciprocal of the total prefix cardinality. -/
theorem publicPrefix_term_probability (bound : Nat) (term : Term (Label Formula))
    (member : term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound) :
    eventMass (fun found => found == term) (publicPrefix api bound) =
      1 / ((SourceSizedQueries.through (fun size : Nat => api.terms size) bound).length : Rat) := by
  rw [publicPrefix_exact]
  exact DistinctRank.Index.uniform_term_probability
    ⟨_, SourceSizedPublicContracts.enumeration_nodup input api success bound,
      fun _ => Iff.rfl⟩ term member

end MicroCFTA.SourceSizedBoundedSampling
