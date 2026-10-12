import MicroCFTA.RecursiveNaryMass
import MicroCFTA.RecursiveRankMass

/-!
# Rank masses for typed n-ary recursive bodies

Rank projection retains duplicate user values and complete term identities.
-/
namespace MicroCFTA.RecursiveNaryRankMass
open Language GeneratorCombinators Probability Sampler SamplerReplay RecursiveNaryBody
open RecursiveRankMass (Related rankMass Same map_left map_right choice_same apply_same empty_same bounded_same ranked_projection)

/-- Lowered alternatives preserve equal child counts and rank distributions. -/
theorem alternatives_same (keys : List Key)
    (left : Key → RecursiveSource.Recipe Root α) (right : Key → RecursiveSource.Recipe Other β)
    (leftEnvironment : Nat → Record Root) (rightEnvironment : Nat → Record Other) (size : Nat)
    (aligned : ∀ key ∈ keys, Same
      (RecursiveSource.record (left key) leftEnvironment size)
      (RecursiveSource.record (right key) rightEnvironment size)) :
    Same (RecursiveSource.record (alternatives (keys.map left)) leftEnvironment size)
      (RecursiveSource.record (alternatives (keys.map right)) rightEnvironment size) := by
  induction keys with
  | nil =>
      simp only [List.map_nil, RecursiveNaryBody.alternatives, RecursiveNaryBody.empty, RecursiveSource.record, FiniteSource.atSize]
      split <;> exact ⟨rfl, rfl⟩
  | cons key rest ih =>
      cases rest with
      | nil => exact aligned key (by simp)
      | cons next later =>
          exact choice_same _ _ (.cons (aligned key (by simp))
            (.cons (ih (fun k present => aligned k (by simp [present]))) .nil))

/-- Each heterogeneous body derives equal value-index counts and rank probabilities. -/
theorem body_values (recipe : Recipe Root Symbol α)
    (paired : Nat → Record (Root × EngineTerm Symbol)) (values : Nat → Record Root)
    (aligned : ∀ size, Same (paired size) (values size)) (size : Nat) :
    Same (RecursiveSource.record (pairedRecipe recipe) paired size)
      (RecursiveSource.record (valueRecipe recipe) values size) := by
  induction recipe generalizing size with
  | finite source => exact map_right _ _ _ ⟨rfl, rfl⟩
  | occurrence => exact aligned size
  | map transform inner ih => exact map_right _ _ _ (map_left _ _ _ (ih size))
  | pay inner ih => cases size with
      | zero => exact empty_same
      | succ size => exact ih size
  | label symbol inner ih => cases size with
      | zero => exact empty_same
      | succ size => exact map_left _ _ _ (ih size)
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_same
      intro index _
      exact map_left _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply choice_same
      have related : ∀ splits : List Nat, Related Same
          (splits.map fun split => applyRecord
            (mapRecord (fun function argument => (function.1 argument.1, Term.node Label.apply [function.2, argument.2]))
              (RecursiveSource.record (pairedRecipe functions) paired split))
            (RecursiveSource.record (pairedRecipe arguments) paired (size - split)))
          (splits.map fun split => applyRecord
            (RecursiveSource.record (valueRecipe functions) values split)
            (RecursiveSource.record (valueRecipe arguments) values (size - split))) := by
        intro splits
        induction splits with
        | nil => exact .nil
        | cons split rest ih => exact .cons (apply_same _ _ _ _ (map_left _ _ _ (ihf split)) (iha _)) ih
      exact related _

/-- Each heterogeneous body derives equal term-index counts and rank probabilities. -/
theorem body_terms (recipe : Recipe Root Symbol α)
    (paired : Nat → Record (Root × EngineTerm Symbol)) (terms : Nat → Record (EngineTerm Symbol))
    (aligned : ∀ size, Same (paired size) (terms size)) (size : Nat) :
    Same (RecursiveSource.record (pairedRecipe recipe) paired size)
      (RecursiveSource.record (termRecipe recipe) terms size) := by
  induction recipe generalizing size with
  | finite source => exact map_right _ _ _ ⟨rfl, rfl⟩
  | occurrence => exact aligned size
  | map transform inner ih => exact map_left _ _ _ (ih size)
  | pay inner ih => cases size with
      | zero => exact empty_same
      | succ size => exact ih size
  | label symbol inner ih => cases size with
      | zero => exact empty_same
      | succ size => exact map_right _ _ _ (map_left _ _ _ (ih size))
  | choice count branches ih =>
      simp only [pairedRecipe, termRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_same
      intro index _
      exact map_right _ _ _ (map_left _ _ _ (ih index size))
  | ap functions arguments ihf iha =>
      apply choice_same
      have related : ∀ splits : List Nat, Related Same
          (splits.map fun split => applyRecord
            (mapRecord (fun function argument => (function.1 argument.1, Term.node Label.apply [function.2, argument.2]))
              (RecursiveSource.record (pairedRecipe functions) paired split))
            (RecursiveSource.record (pairedRecipe arguments) paired (size - split)))
          (splits.map fun split => applyRecord
            (mapRecord (fun function argument => Term.node Label.apply [function, argument])
              (RecursiveSource.record (termRecipe functions) terms split))
            (RecursiveSource.record (termRecipe arguments) terms (size - split))) := by
        intro splits
        induction splits with
        | nil => exact .nil
        | cons split rest ih =>
            exact .cons (apply_same _ _ _ _ (map_right _ _ _ (map_left _ _ _ (ihf split))) (iha _)) ih
      exact related _

/-- Actual recursive value records keep the paired record's exact rank masses. -/
theorem family_values (body : Recipe Root Symbol Root) (size : Nat) :
    Same (RecursiveSource.family (pairedBody body) size) (RecursiveSource.family (valueRecipe body) size) := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.family, RecursiveSource.family]
      apply map_left
      apply body_values
      intro childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller] using ih childSize smaller
      · simpa only [dite_eq_right smaller] using (empty_same (α := Root × EngineTerm Symbol) (β := Root))

/-- Actual recursive term records keep the paired record's exact rank masses. -/
theorem family_terms (body : Recipe Root Symbol Root) (size : Nat) :
    Same (RecursiveSource.family (pairedBody body) size) (RecursiveSource.family (termBody body) size) := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.family, RecursiveSource.family]
      apply map_right
      apply map_left
      apply body_terms
      intro childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller] using ih childSize smaller
      · simpa only [dite_eq_right smaller] using (empty_same (α := Root × EngineTerm Symbol) (β := EngineTerm Symbol))

/-- The public bounded value and term records retain the same mass at every rank. -/
theorem bounded_rank_masses (body : Recipe Root Symbol Root) (bound : Nat) :
    rankMass (RecursiveSource.bounded (valueRecipe body) bound) =
      rankMass (RecursiveSource.bounded (termBody body) bound) := by
  have values := bounded_same _ _ (family_values body) bound
  have terms := bounded_same _ _ (family_terms body) bound
  exact values.2.symm.trans terms.2

/-- The actual value sampler retains the paired record's value at each sampled rank and mass. -/
theorem ranked_values (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (RecursiveSource.family (pairedBody body) size).sampling.ranked =
        (RecursiveSource.family (valueRecipe body) size).sampling.ranked :=
  ranked_projection Prod.fst _ _ _ _ (RecursiveSource.family_live (pairedBody body) size).1.2
    (RecursiveSource.family_live (valueRecipe body) size).1.2
    (RecursiveNaryBody.decode_value body size) (family_values body size).2

/-- The actual term sampler retains the paired record's term at each sampled rank and mass. -/
theorem ranked_terms (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (RecursiveSource.family (pairedBody body) size).sampling.ranked =
        (RecursiveSource.family (termBody body) size).sampling.ranked :=
  ranked_projection Prod.snd _ _ _ _ (RecursiveSource.family_live (pairedBody body) size).1.2
    (RecursiveSource.family_live (termBody body) size).1.2
    (RecursiveNaryBody.decode_term body size) (family_terms body size).2

/-- Bounded value sampling preserves the common sampled rank, value, and exact mass. -/
theorem bounded_ranked_values (body : Recipe Root Symbol Root) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (RecursiveSource.bounded (pairedBody body) bound).sampling.ranked =
        (RecursiveSource.bounded (valueRecipe body) bound).sampling.ranked := by
  apply ranked_projection Prod.fst _ _ _ _ (RecursiveSource.bounded_live (pairedBody body) bound).1.2
    (RecursiveSource.bounded_live (valueRecipe body) bound).1.2
  · intro rank
    simp only [Decoder.decode_correct]
    rw [← RecursiveNaryBody.bounded_values body bound, List.getElem?_map]
  · exact (bounded_same _ _ (family_values body) bound).2

/-- Bounded term sampling preserves the common sampled rank, term, and exact mass. -/
theorem bounded_ranked_terms (body : Recipe Root Symbol Root) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (RecursiveSource.bounded (pairedBody body) bound).sampling.ranked =
        (RecursiveSource.bounded (termBody body) bound).sampling.ranked := by
  apply ranked_projection Prod.snd _ _ _ _ (RecursiveSource.bounded_live (pairedBody body) bound).1.2
    (RecursiveSource.bounded_live (termBody body) bound).1.2
  · intro rank
    simp only [Decoder.decode_correct]
    rw [← RecursiveNaryBody.bounded_terms body bound, List.getElem?_map]
  · exact (bounded_same _ _ (family_terms body) bound).2


end MicroCFTA.RecursiveNaryRankMass
