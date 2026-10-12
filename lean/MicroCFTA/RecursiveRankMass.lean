import MicroCFTA.RecursiveTermMass

/-!
# Recursive rank probabilities across independently built records

Equal values can hide a change in rank probabilities. These results retain
the sampled rank and compare its exact mass before value projection.
-/
namespace MicroCFTA.RecursiveRankMass
open Language GeneratorCombinators Probability Sampler SamplerReplay RecursiveTermAlignment

/-- Relate ordered record lists without restricting their value universes. -/
inductive Related {α : Type u} {β : Type v} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Related relation [] []
  | cons : relation a b → Related relation as bs → Related relation (a :: as) (b :: bs)

/-- The exact probability of each replay rank, with all sampler runs retained. -/
def rankMass (record : Record α) : Distribution Nat := Probability.map Prod.fst record.sampling.ranked

/-- Records with different value types can have the same count and rank law. -/
def Same (left : Record α) (right : Record β) : Prop :=
  Decoder.count left.plan = Decoder.count right.plan ∧ rankMass left = rankMass right

/-- Value mapping keeps the complete rank distribution. -/
theorem map_rankMass (transform : α → β) (record : Record α) :
    rankMass (mapRecord transform record) = rankMass record := by
  simp [rankMass, mapRecord, mapSampler, Probability.map, List.map_map, Function.comp_def]

theorem map_left (transform : α → β) (left : Record α) (right : Record γ) (same : Same left right) :
    Same (mapRecord transform left) right :=
  ⟨same.1, (map_rankMass transform left).trans same.2⟩

theorem map_right (transform : β → γ) (left : Record α) (right : Record β) (same : Same left right) :
    Same left (mapRecord transform right) :=
  ⟨same.1, same.2.trans (map_rankMass transform right).symm⟩

/-- Product rank probabilities use only the two input rank laws and the right count. -/
theorem apply_rankMass (functions : Record (α → β)) (arguments : Record α) :
    rankMass (applyRecord functions arguments) =
      Probability.map (fun pair => pairRank (Decoder.count arguments.plan) pair.1 pair.2)
        (Probability.product (rankMass functions) (rankMass arguments)) := by
  simp [rankMass, applyRecord, productSampler, Probability.map, Probability.product,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem apply_same (firstFunctions : Record (α → β)) (firstArguments : Record α)
    (secondFunctions : Record (γ → δ)) (secondArguments : Record γ)
    (functions : Same firstFunctions secondFunctions) (arguments : Same firstArguments secondArguments) :
    Same (applyRecord firstFunctions firstArguments) (applyRecord secondFunctions secondArguments) := by
  constructor
  · change Decoder.count firstFunctions.plan * Decoder.count firstArguments.plan = _
    change _ = Decoder.count secondFunctions.plan * Decoder.count secondArguments.plan
    rw [functions.1, arguments.1]
  · rw [apply_rankMass, apply_rankMass, functions.2, arguments.2, arguments.1]

/-- The actual live choice rows retain structural offsets through skipped branches. -/
def rankRows (offset : Nat) : List (Rat × Record α) → List (Rat × Distribution Nat)
  | [] => []
  | (mass, record) :: rest =>
      let later := rankRows (offset + Decoder.count record.plan) rest
      if 0 < Decoder.count record.plan ∧ 0 < mass then
        (mass, Probability.map (offset + ·) (rankMass record)) :: later
      else later

/-- The sampler's stored choice parts have exactly the rank-only rows above. -/
theorem parts_rankRows (records : List (Rat × Record α)) (offset : Nat) :
    (choiceParts offset (alternatives records)).map (fun part =>
      (part.mass, Probability.map Prod.fst
        (Probability.map (fun entry => (part.offset + entry.1, entry.2)) part.sampling.ranked))) =
      rankRows offset records := by
  induction records generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      simp only [alternatives, List.map_cons, choiceParts, rankRows]
      split
      · simp only [List.map_cons]
        congr 1
        · simp [rankMass, Probability.map, List.map_map, Function.comp_def]
        · exact ih _
      · exact ih _

/-- Exact n-way rank sampling normalizes the source rows and their declared masses. -/
theorem many_rankMass (records : List (Rat × Record α)) :
    rankMass (manyRecord records) = Probability.frequency (rankRows 0 records) := by
  simp only [rankMass, manyRecord, chooseSampler, map_frequency, List.map_map, Function.comp_def]
  rw [parts_rankRows]

theorem rows_same (left : List (Rat × Record α)) (right : List (Rat × Record β))
    (same : Related (fun first second => first.1 = second.1 ∧ Same first.2 second.2) left right)
    (offset : Nat) : rankRows offset left = rankRows offset right := by
  induction same generalizing offset with
  | nil => rfl
  | @cons first second restLeft restRight related remaining ih =>
      simp only [rankRows]
      rw [related.1, related.2.1, related.2.2, ih]

/-- Count-weighted choice preserves matching rank laws for arbitrary value types. -/
theorem choice_same (left : List (Record α)) (right : List (Record β))
    (same : Related Same left right) : Same (FiniteSource.countChoice left) (FiniteSource.countChoice right) := by
  constructor
  · induction same with
    | nil => rfl
    | cons related remaining ih =>
        simp only [FiniteSource.countChoice, manyRecord, List.map_cons, manyPlan, Decoder.count] at ih ⊢
        rw [related.1, ih]
  · rw [FiniteSource.countChoice, FiniteSource.countChoice, many_rankMass, many_rankMass]
    congr 1
    apply rows_same
    induction same with
    | nil => exact .nil
    | cons related remaining ih =>
        exact .cons ⟨congrArg (fun n : Nat => (n : Rat)) related.1, related⟩ ih

theorem empty_same : Same (FiniteSource.empty : Record α) (FiniteSource.empty : Record β) := ⟨rfl, rfl⟩

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
  | choice left right ihl ihr =>
      exact choice_same _ _ (.cons (map_left _ _ _ (ihl size)) (.cons (map_left _ _ _ (ihr size)) .nil))
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
  | choice left right ihl ihr =>
      exact choice_same _ _ (.cons (map_right _ _ _ (map_left _ _ _ (ihl size)))
        (.cons (map_right _ _ _ (map_left _ _ _ (ihr size))) .nil))
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

/-- A complete class prefix preserves counts and exact rank masses. -/
theorem bounded_same (left : Nat → Record α) (right : Nat → Record β)
    (aligned : ∀ size, Same (left size) (right size)) (bound : Nat) :
    Same (boundedRecord left bound) (boundedRecord right bound) := by
  have related : ∀ sizes : List Nat, Related Same (sizes.map left) (sizes.map right) := by
    intro sizes
    induction sizes with
    | nil => exact .nil
    | cons size rest ih => exact .cons (aligned size) ih
  simpa only [FiniteSource.countChoice, boundedRecord, List.map_map, Function.comp_def] using
    (choice_same _ _ (related (List.range (bound + 1))))

/-- The public bounded value and term records retain the same mass at every rank. -/
theorem bounded_rank_masses (body : Recipe Root Symbol Root) (bound : Nat) :
    rankMass (RecursiveSource.bounded (valueRecipe body) bound) =
      rankMass (RecursiveSource.bounded (termBody body) bound) := by
  have values := bounded_same _ _ (family_values body) bound
  have terms := bounded_same _ _ (family_terms body) bound
  exact values.2.symm.trans terms.2

/-- Replay and a rank law determine the entire ranked distribution, even with duplicate values. -/
theorem ranked_projection (transform : α → β) (left : Distribution (Nat × α))
    (right : Distribution (Nat × β)) (first : Nat → Option α) (second : Nat → Option β)
    (firstReplay : Replays first left) (secondReplay : Replays second right)
    (decoders : ∀ rank, (first rank).map transform = second rank)
    (masses : Probability.map Prod.fst left = Probability.map Prod.fst right) :
    Probability.map (fun entry => (entry.1, transform entry.2)) left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [Probability.map]
  | cons entry rest ih =>
      cases right with
      | nil => simp [Probability.map] at masses
      | cons other tail =>
          have firstHead := firstReplay entry (by simp)
          have secondHead := secondReplay other (by simp)
          simp only [Probability.map, List.map_cons, List.cons.injEq, Prod.mk.injEq] at masses
          obtain ⟨⟨sameMass, sameRank⟩, sameTail⟩ := masses
          have sameValue := decoders entry.2.1
          rw [firstHead, sameRank, secondHead] at sameValue
          have valueEq : transform entry.2.2 = other.2.2 := Option.some.inj sameValue
          simp only [Probability.map, List.map_cons]
          rw [List.cons.injEq]
          constructor
          · exact Prod.ext sameMass (Prod.ext sameRank valueEq)
          · exact ih tail (fun item member => firstReplay item (by simp [member]))
              (fun item member => secondReplay item (by simp [member])) sameTail

/-- The actual value sampler retains the paired record's value at each sampled rank and mass. -/
theorem ranked_values (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (RecursiveSource.family (pairedBody body) size).sampling.ranked =
        (RecursiveSource.family (valueRecipe body) size).sampling.ranked :=
  ranked_projection Prod.fst _ _ _ _ (RecursiveSource.family_live (pairedBody body) size).1.2
    (RecursiveSource.family_live (valueRecipe body) size).1.2
    (RecursiveTermAlignment.decode_value body size) (family_values body size).2

/-- The actual term sampler retains the paired record's term at each sampled rank and mass. -/
theorem ranked_terms (body : Recipe Root Symbol Root) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (RecursiveSource.family (pairedBody body) size).sampling.ranked =
        (RecursiveSource.family (termBody body) size).sampling.ranked :=
  ranked_projection Prod.snd _ _ _ _ (RecursiveSource.family_live (pairedBody body) size).1.2
    (RecursiveSource.family_live (termBody body) size).1.2
    (RecursiveTermAlignment.decode_term body size) (family_terms body size).2

/-- Bounded value sampling preserves the common sampled rank, value, and exact mass. -/
theorem bounded_ranked_values (body : Recipe Root Symbol Root) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (RecursiveSource.bounded (pairedBody body) bound).sampling.ranked =
        (RecursiveSource.bounded (valueRecipe body) bound).sampling.ranked := by
  apply ranked_projection Prod.fst _ _ _ _ (RecursiveSource.bounded_live (pairedBody body) bound).1.2
    (RecursiveSource.bounded_live (valueRecipe body) bound).1.2
  · intro rank
    simp only [Decoder.decode_correct]
    rw [← RecursiveTermAlignment.bounded_values body bound, List.getElem?_map]
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
    rw [← RecursiveTermAlignment.bounded_terms body bound, List.getElem?_map]
  · exact (bounded_same _ _ (family_terms body) bound).2

end MicroCFTA.RecursiveRankMass
