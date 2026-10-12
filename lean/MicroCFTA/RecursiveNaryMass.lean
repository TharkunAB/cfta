import MicroCFTA.RecursiveNaryBody

/-!
# Correlated mass fields for typed n-ary recursive bodies

Each projection retains every sampler run and its mass. Choice lowering
keeps the same ordered list of source branch numbers in the paired fields.
-/
namespace MicroCFTA.RecursiveNaryMass
open Language GeneratorCombinators RecursiveNaryBody Probability
open RecursiveTermMass (map_choice map_compose)

/-- Equal child counts give equal counts for the complete ordered choice. -/
theorem alternatives_counts (keys : List Key)
    (left : Key → RecursiveSource.Recipe Root α) (right : Key → RecursiveSource.Recipe Other β)
    (leftMembers : Nat → List Root) (rightMembers : Nat → List Other) (size : Nat)
    (same : ∀ key ∈ keys,
      (RecursiveSource.values (left key) leftMembers size).length =
        (RecursiveSource.values (right key) rightMembers size).length) :
    (RecursiveSource.values (alternatives (keys.map left)) leftMembers size).length =
      (RecursiveSource.values (alternatives (keys.map right)) rightMembers size).length := by
  simp only [alternatives_values, List.flatMap_map, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  exact same

/-- Mapping each choice distribution maps the complete lowered choice. -/
theorem alternatives_map (keys : List Key)
    (left : Key → RecursiveSource.Recipe Root α) (right : Key → RecursiveSource.Recipe Other β)
    (leftMembers : Nat → List Root) (rightMembers : Nat → List Other)
    (leftMasses : Nat → Distribution Root) (rightMasses : Nat → Distribution Other)
    (size : Nat) (transform : α → β)
    (counts : ∀ key ∈ keys,
      (RecursiveSource.values (left key) leftMembers size).length =
        (RecursiveSource.values (right key) rightMembers size).length)
    (mapped : ∀ key ∈ keys,
      Probability.map transform (RecursiveSource.probabilities (left key) leftMembers leftMasses size) =
        RecursiveSource.probabilities (right key) rightMembers rightMasses size) :
    Probability.map transform
        (RecursiveSource.probabilities (alternatives (keys.map left)) leftMembers leftMasses size) =
      RecursiveSource.probabilities (alternatives (keys.map right)) rightMembers rightMasses size := by
  induction keys with
  | nil =>
      simp [alternatives, empty, RecursiveSource.probabilities, FiniteSource.classDistribution, Probability.map, normalize, counting, scale]
  | cons key rest ih =>
      cases rest with
      | nil => simpa [alternatives] using mapped key (by simp)
      | cons next later =>
          have headCount := counts key (by simp)
          have tailCount := alternatives_counts (next :: later) left right leftMembers rightMembers size
            (fun k present => counts k (by simp [present]))
          have headMapped := mapped key (by simp)
          have tailMapped := ih (fun k present => counts k (by simp [present]))
            (fun k present => mapped k (by simp [present]))
          simp only [List.map_cons, alternatives, RecursiveSource.probabilities,
            map_choice, List.map_cons, List.map_nil] at *
          rw [headCount, tailCount, headMapped, tailMapped]

/-- Each value mass is the projection of its paired sampler run. -/
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
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_map
      · intro index _
        simpa only [RecursiveSource.values, List.length_map] using
          congrArg List.length (RecursiveNaryBody.body_values (branches index) members size)
      · intro index _
        simpa only [RecursiveSource.probabilities, map_compose] using ih index size
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, valueRecipe, RecursiveSource.probabilities, map_choice, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro split _
      have firstCount := congrArg List.length (RecursiveNaryBody.body_values functions members split)
      have secondCount := congrArg List.length (RecursiveNaryBody.body_values arguments members (size - split))
      simp only [RecursiveSource.values, List.length_map] at firstCount secondCount ⊢
      rw [← firstCount, ← secondCount, ← ihf split, ← iha (size - split)]
      simp [Probability.map, Probability.product, List.map_flatMap, List.flatMap_map,
        List.map_map, Function.comp_def]

/-- Each term mass retains its flat branch number and paired sampler run. -/
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
  | choice count branches ih =>
      simp only [pairedRecipe, termRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_map
      · intro index _
        simpa only [RecursiveSource.values, List.length_map] using
          congrArg List.length (RecursiveNaryBody.body_terms (branches index) members size)
      · intro index _
        simpa only [RecursiveSource.probabilities, map_compose] using
          congrArg (Probability.map (wrap index.val)) (ih index size)
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, termRecipe, RecursiveSource.probabilities, map_choice, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro split _
      have firstCount := congrArg List.length (RecursiveNaryBody.body_terms functions members split)
      have secondCount := congrArg List.length (RecursiveNaryBody.body_terms arguments members (size - split))
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
        · simpa only [ite_eq_left smaller, pairedBody] using RecursiveNaryBody.family_values body childSize
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
        · simpa only [ite_eq_left smaller, pairedBody, termBody] using RecursiveNaryBody.family_terms body childSize
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
  have count := congrArg List.length (RecursiveNaryBody.family_values body size)
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
  have count := congrArg List.length (RecursiveNaryBody.family_terms body size)
  simp only [List.length_map] at count
  simp [count, family_terms]


end MicroCFTA.RecursiveNaryMass
