import MicroCFTA.RecursiveTermAlignment

/-!
# Recursive value and term probability alignment

Projection retains each run's mass. The source chooses recursive branches
and size splits by counts and retains the finite atomic distributions.
-/
namespace MicroCFTA.RecursiveTermMass
open Language GeneratorCombinators RecursiveTermAlignment Probability

/-- Mapping outcomes commutes with the source live-branch filter and chooser. -/
theorem map_choice (transform : α → β) (branches : List (Nat × Rat × Distribution α)) :
    Probability.map transform (SamplerReplay.weightedChoice branches) =
      SamplerReplay.weightedChoice
        (branches.map fun entry => (entry.1, entry.2.1, Probability.map transform entry.2.2)) := by
  rw [SamplerReplay.weightedChoice, Sampler.map_frequency, SamplerReplay.weightedChoice]
  congr 1
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      by_cases live : 0 < first.1 ∧ 0 < first.2.1
      · simp [live, ih]
      · simp [live, ih]

/-- Consecutive value maps retain all original run masses. -/
theorem map_compose (first : α → β) (second : β → γ) (outcomes : Distribution α) :
    Probability.map second (Probability.map first outcomes) =
      Probability.map (fun value => second (first value)) outcomes := by
  simp [Probability.map, List.map_map, Function.comp_def]

/-- The value probability field follows the same constructor schedule as its paired field. -/
theorem body_values (recipe : Recipe Root Symbol α)
    (members : Nat → List (Root × EngineTerm Symbol))
    (masses : Nat → Distribution (Root × EngineTerm Symbol)) (size : Nat) :
    Probability.map Prod.fst (RecursiveSource.probabilities (pairedRecipe recipe) members masses size) =
      RecursiveSource.probabilities (valueRecipe recipe)
        (fun size => (members size).map Prod.fst) (fun size => Probability.map Prod.fst (masses size)) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih =>
      simpa [pairedRecipe, valueRecipe, RecursiveSource.probabilities,
        Probability.map, List.map_map, Function.comp_def] using congrArg (Probability.map transform) (ih size)
  | pay inner ih => cases size with
      | zero => rfl
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => rfl
      | succ size => simpa [pairedRecipe, valueRecipe, RecursiveSource.probabilities,
          Probability.map, List.map_map, Function.comp_def] using ih size
  | choice left right ihl ihr =>
      simp only [pairedRecipe, valueRecipe, RecursiveSource.probabilities, map_choice, List.map_cons, List.map_nil]
      have leftCount := congrArg List.length (RecursiveTermAlignment.body_values left members size)
      have rightCount := congrArg List.length (RecursiveTermAlignment.body_values right members size)
      simp only [RecursiveSource.values, List.length_map] at leftCount rightCount ⊢
      rw [← leftCount, ← rightCount, ← ihl size, ← ihr size]
      simp [Probability.map, List.map_map, Function.comp_def]
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, valueRecipe, RecursiveSource.probabilities, map_choice, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro split _
      have firstCount := congrArg List.length (RecursiveTermAlignment.body_values functions members split)
      have secondCount := congrArg List.length (RecursiveTermAlignment.body_values arguments members (size - split))
      simp only [RecursiveSource.values, List.length_map] at firstCount secondCount ⊢
      rw [← firstCount, ← secondCount, ← ihf split, ← iha (size - split)]
      simp [Probability.map, Probability.product, List.map_flatMap, List.flatMap_map,
        List.map_map, Function.comp_def]

/-- The independently constructed term sampler is the paired sampler's term marginal. -/
theorem body_terms (recipe : Recipe Root Symbol α)
    (members : Nat → List (Root × EngineTerm Symbol))
    (masses : Nat → Distribution (Root × EngineTerm Symbol)) (size : Nat) :
    Probability.map Prod.snd (RecursiveSource.probabilities (pairedRecipe recipe) members masses size) =
      RecursiveSource.probabilities (termRecipe recipe)
        (fun size => (members size).map Prod.snd) (fun size => Probability.map Prod.snd (masses size)) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih =>
      simpa [pairedRecipe, termRecipe, RecursiveSource.probabilities,
        Probability.map, List.map_map, Function.comp_def] using ih size
  | pay inner ih => cases size with
      | zero => rfl
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => rfl
      | succ size =>
          simpa [pairedRecipe, termRecipe, RecursiveSource.probabilities,
            Probability.map, List.map_map, Function.comp_def] using
            (congrArg (Probability.map (SupportTerms.labelTerm symbol)) (ih size))
  | choice left right ihl ihr =>
      simp only [pairedRecipe, termRecipe, RecursiveSource.probabilities, map_choice, List.map_cons, List.map_nil]
      have leftCount := congrArg List.length (RecursiveTermAlignment.body_terms left members size)
      have rightCount := congrArg List.length (RecursiveTermAlignment.body_terms right members size)
      simp only [RecursiveSource.values, List.length_map] at leftCount rightCount ⊢
      rw [← leftCount, ← rightCount, ← ihl size, ← ihr size]
      simp [Probability.map, List.map_map, Function.comp_def]
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, termRecipe, RecursiveSource.probabilities, map_choice, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro split _
      have firstCount := congrArg List.length (RecursiveTermAlignment.body_terms functions members split)
      have secondCount := congrArg List.length (RecursiveTermAlignment.body_terms arguments members (size - split))
      simp only [RecursiveSource.values, List.length_map] at firstCount secondCount ⊢
      rw [← firstCount, ← secondCount, ← ihf split, ← iha (size - split)]
      simp [Probability.map, Probability.product, List.map_flatMap, List.flatMap_map,
        List.map_map, Function.comp_def]

/-- Recursive class probabilities keep the complete value marginal in source order. -/
theorem family_values (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map Prod.fst (RecursiveSource.classProbability (pairedBody body) size) =
      RecursiveSource.classProbability (valueRecipe body) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.classProbability, RecursiveSource.classProbability]
      simp only [pairedBody, RecursiveSource.probabilities, map_compose]
      rw [body_values]
      congr 1
      · funext childSize
        by_cases smaller : childSize < size
        · simpa only [ite_eq_left smaller, pairedBody] using RecursiveTermAlignment.family_values body childSize
        · simp [smaller]
      · funext childSize
        by_cases smaller : childSize < size
        · simpa only [dite_eq_left smaller, ite_eq_left smaller, pairedBody] using ih childSize smaller
        · simp [smaller, Probability.map]

/-- Recursive class probabilities keep the complete constructor-term marginal. -/
theorem family_terms (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map Prod.snd (RecursiveSource.classProbability (pairedBody body) size) =
      RecursiveSource.classProbability (termBody body) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.classProbability, RecursiveSource.classProbability]
      simp only [pairedBody, termBody, RecursiveSource.probabilities, map_compose]
      have step := congrArg (Probability.map (fun term : EngineTerm Symbol => Term.node Label.recursion [term]))
        (body_terms body
          (fun childSize => if childSize < size then RecursiveSource.languageClass (pairedBody body) childSize else [])
          (fun childSize => if childSize < size then RecursiveSource.classProbability (pairedBody body) childSize else []) size)
      simp only [map_compose, pairedBody] at step
      simp only [dite_eq_ite]
      rw [step]
      congr 2
      · funext childSize
        by_cases smaller : childSize < size
        · simpa only [ite_eq_left smaller, pairedBody, termBody] using RecursiveTermAlignment.family_terms body childSize
        · simp [smaller]
      · funext childSize
        by_cases smaller : childSize < size
        · simpa only [ite_eq_left smaller, pairedBody, termBody] using ih childSize smaller
        · simp [smaller, Probability.map]

/-- The executable value sampler is the correlated record's value marginal. -/
theorem value_sampler (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map Prod.fst (RecursiveSource.family (pairedBody body) size).sampling.values =
      (RecursiveSource.family (valueRecipe body) size).sampling.values := by
  simp only [RecursiveSource.family_probability, family_values]

/-- The executable term sampler is the correlated record's term marginal. -/
theorem term_sampler (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map Prod.snd (RecursiveSource.family (pairedBody body) size).sampling.values =
      (RecursiveSource.family (termBody body) size).sampling.values := by
  simp only [RecursiveSource.family_probability, family_terms]

/-- The bounded value sampler keeps count-weighted classes and their internal masses. -/
theorem bounded_values (body : Recipe Root Symbol Root) (bound : Nat) :
    Probability.map Prod.fst (RecursiveSource.bounded (pairedBody body) bound).sampling.values =
      (RecursiveSource.bounded (valueRecipe body) bound).sampling.values := by
  rw [RecursiveSource.bounded_probability, map_choice, RecursiveSource.bounded_probability]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro size _
  have count := congrArg List.length (RecursiveTermAlignment.family_values body size)
  simp only [List.length_map] at count
  simp [count, family_values]

/-- The bounded term sampler keeps the same exact term probabilities. -/
theorem bounded_terms (body : Recipe Root Symbol Root) (bound : Nat) :
    Probability.map Prod.snd (RecursiveSource.bounded (pairedBody body) bound).sampling.values =
      (RecursiveSource.bounded (termBody body) bound).sampling.values := by
  rw [RecursiveSource.bounded_probability, map_choice, RecursiveSource.bounded_probability]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro size _
  have count := congrArg List.length (RecursiveTermAlignment.family_terms body size)
  simp only [List.length_map] at count
  simp [count, family_terms]

end MicroCFTA.RecursiveTermMass
