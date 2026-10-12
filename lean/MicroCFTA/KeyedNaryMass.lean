import MicroCFTA.KeyedNaryAlignment
import MicroCFTA.KeyedTermMass

/-!
# Exact mass and rank fields of n-ary keyed families

Each key retains its unnormalized mass and full conditional rank law.
Flat branch numbers are fixed before the source algebra lowering.
-/
namespace MicroCFTA.KeyedNaryMass
open Language GeneratorCombinators Probability SamplerReplay KeyedNaryAlignment
open RecursiveRankMass (Related rankMass map_right ranked_projection bounded_same)
open KeyedTermMass (SameGroup map_left_group map_right_group counted_same retained_same apply_group merge_same empty_group)

/-- Lowered alternatives preserve each child mass, count, and complete rank law. -/
theorem alternatives_same (labels : List Name)
    (left : Name → KeyedSource.Recipe Key Root α) (right : Name → KeyedSource.Recipe Key Other β)
    (leftEnvironment : Key → GroupedRecord.Classes Root) (rightEnvironment : Key → GroupedRecord.Classes Other)
    (size : Nat) (aligned : ∀ label ∈ labels, SameGroup
      (KeyedSource.record (left label) leftEnvironment size) (KeyedSource.record (right label) rightEnvironment size)) :
    SameGroup (KeyedSource.record (KeyedNaryAlignment.alternatives (labels.map left)) leftEnvironment size)
      (KeyedSource.record (KeyedNaryAlignment.alternatives (labels.map right)) rightEnvironment size) := by
  induction labels with
  | nil =>
      simp only [List.map_nil, KeyedNaryAlignment.alternatives, KeyedNaryAlignment.empty, KeyedSource.record,
        GroupedRecord.finiteClass, FiniteSource.atSize]
      split <;> exact ⟨rfl, rfl, rfl⟩
  | cons label rest ih =>
      cases rest with
      | nil => exact aligned label (by simp)
      | cons next later =>
          exact merge_same _ _ (.cons (aligned label (by simp))
            (.cons (ih (fun k present => aligned k (by simp [present]))) .nil))

/-- Every typed body constructs the same key mass and value-index rank law. -/
theorem body_values (recipe : Recipe Key Root Symbol α)
    (paired : Key → GroupedRecord.Classes (Root × EngineTerm Symbol)) (values : Key → GroupedRecord.Classes Root)
    (aligned : ∀ key size, SameGroup (paired key size) (values key size)) (size : Nat) :
    SameGroup (KeyedSource.record (pairedRecipe recipe) paired size)
      (KeyedSource.record (valueRecipe recipe) values size) := by
  induction recipe generalizing size with
  | finite source => exact counted_same _ _ (map_right _ _ _ ⟨rfl, rfl⟩)
  | retained mass positive source => exact retained_same _ _ _ (map_right _ _ _ ⟨rfl, rfl⟩)
  | occurrence key => exact aligned key size
  | map transform inner ih => exact map_right_group _ _ _ (map_left_group _ _ _ (ih size))
  | pay inner ih => cases size with
      | zero => exact empty_group
      | succ size => exact ih size
  | label symbol inner ih => cases size with
      | zero => exact empty_group
      | succ size => exact map_left_group _ _ _ (ih size)
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_same
      intro index _
      exact map_left_group _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply merge_same
      have related : ∀ splits : List Nat, Related SameGroup
          (splits.map fun split => GroupedRecord.apply
            (GroupedRecord.map (fun function argument => (function.1 argument.1, Term.node Label.apply [function.2, argument.2]))
              (KeyedSource.record (pairedRecipe functions) paired split))
            (KeyedSource.record (pairedRecipe arguments) paired (size - split)))
          (splits.map fun split => GroupedRecord.apply
            (KeyedSource.record (valueRecipe functions) values split)
            (KeyedSource.record (valueRecipe arguments) values (size - split))) := by
        intro splits
        induction splits with
        | nil => exact .nil
        | cons split rest ih => exact .cons (apply_group _ _ _ _ (map_left_group _ _ _ (ihf split)) (iha _)) ih
      exact related _

/-- Every typed body constructs the same key mass and independent term-index rank law. -/
theorem body_terms (recipe : Recipe Key Root Symbol α)
    (paired : Key → GroupedRecord.Classes (Root × EngineTerm Symbol)) (terms : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (aligned : ∀ key size, SameGroup (paired key size) (terms key size)) (size : Nat) :
    SameGroup (KeyedSource.record (pairedRecipe recipe) paired size)
      (KeyedSource.record (termRecipe recipe) terms size) := by
  induction recipe generalizing size with
  | finite source => exact counted_same _ _ (map_right _ _ _ ⟨rfl, rfl⟩)
  | retained mass positive source => exact retained_same _ _ _ (map_right _ _ _ ⟨rfl, rfl⟩)
  | occurrence key => exact aligned key size
  | map transform inner ih => exact map_left_group _ _ _ (ih size)
  | pay inner ih => cases size with
      | zero => exact empty_group
      | succ size => exact ih size
  | label symbol inner ih => cases size with
      | zero => exact empty_group
      | succ size => exact map_right_group _ _ _ (map_left_group _ _ _ (ih size))
  | choice count branches ih =>
      simp only [pairedRecipe, termRecipe]
      have indexed {T : Type 1} (f : Fin count → T) : List.ofFn f = (List.ofFn id).map f := by simp [List.map_ofFn]
      rw [indexed, indexed]
      apply alternatives_same
      intro index _
      exact map_right_group _ _ _ (map_left_group _ _ _ (ih index size))
  | ap functions arguments ihf iha =>
      apply merge_same
      have related : ∀ splits : List Nat, Related SameGroup
          (splits.map fun split => GroupedRecord.apply
            (GroupedRecord.map (fun function argument => (function.1 argument.1, Term.node Label.apply [function.2, argument.2]))
              (KeyedSource.record (pairedRecipe functions) paired split))
            (KeyedSource.record (pairedRecipe arguments) paired (size - split)))
          (splits.map fun split => GroupedRecord.apply
            (GroupedRecord.map (fun function argument => Term.node Label.apply [function, argument])
              (KeyedSource.record (termRecipe functions) terms split))
            (KeyedSource.record (termRecipe arguments) terms (size - split))) := by
        intro splits
        induction splits with
        | nil => exact .nil
        | cons split rest ih =>
            exact .cons (apply_group _ _ _ _ (map_right_group _ _ _ (map_left_group _ _ _ (ihf split))) (iha _)) ih
      exact related _

/-- Each key's mutually recursive value record retains the same mass and rank probabilities. -/
theorem family_values (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    SameGroup (KeyedSource.family (pairedProgram wrap program) size key)
      (KeyedSource.family (valueProgram program) size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.family, KeyedSource.family]
      apply map_left_group
      apply body_values
      intro childKey childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller] using ih childSize smaller childKey
      · simpa only [dite_eq_right smaller] using
          (empty_group (α := Root × EngineTerm Symbol) (β := Root))

/-- Each independently tied term record has the same group mass and ranked distribution. -/
theorem family_terms (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    SameGroup (KeyedSource.family (pairedProgram wrap program) size key)
      (KeyedSource.family (termProgram wrap program) size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.family, KeyedSource.family]
      apply map_right_group
      apply map_left_group
      apply body_terms
      intro childKey childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller] using ih childSize smaller childKey
      · simpa only [dite_eq_right smaller] using
          (empty_group (α := Root × EngineTerm Symbol) (β := EngineTerm Symbol))

/-- The full value sampler preserves each shared rank, sampled value, and exact probability. -/
theorem ranked_values (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (KeyedSource.family (pairedProgram wrap program) size key).members.sampling.ranked =
        (KeyedSource.family (valueProgram program) size key).members.sampling.ranked :=
  ranked_projection Prod.fst _ _ _ _ (KeyedSource.family_valid (pairedProgram wrap program) size key).1.1.2
    (KeyedSource.family_valid (valueProgram program) size key).1.1.2
    (fun rank => decode_value wrap program size rank key) (family_values wrap program size key).2.2

/-- The independently built term sampler preserves the paired term at every sampled rank and mass. -/
theorem ranked_terms (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (KeyedSource.family (pairedProgram wrap program) size key).members.sampling.ranked =
        (KeyedSource.family (termProgram wrap program) size key).members.sampling.ranked :=
  ranked_projection Prod.snd _ _ _ _ (KeyedSource.family_valid (pairedProgram wrap program) size key).1.1.2
    (KeyedSource.family_valid (termProgram wrap program) size key).1.1.2
    (fun rank => decode_term wrap program size rank key) (family_terms wrap program size key).2.2

/-- Bounding selects sizes by count and preserves the full value rank distribution. -/
theorem bounded_ranked_values (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (key : Key) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram wrap program) size key) bound).sampling.ranked =
        (GroupedRecord.bounded (fun size => KeyedSource.family (valueProgram program) size key) bound).sampling.ranked := by
  apply ranked_projection Prod.fst _ _ _ _
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
  · intro rank
    simp only [Decoder.decode_correct]
    rw [← bounded_values wrap program key bound, List.getElem?_map]
  · exact (bounded_same _ _ (fun size => (family_values wrap program size key).2) bound).2

/-- Bounded term decoding and exact probabilities retain the same global size-major ranks. -/
theorem bounded_ranked_terms (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (key : Key) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram wrap program) size key) bound).sampling.ranked =
        (GroupedRecord.bounded (fun size => KeyedSource.family (termProgram wrap program) size key) bound).sampling.ranked := by
  apply ranked_projection Prod.snd _ _ _ _
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
  · intro rank
    simp only [Decoder.decode_correct]
    rw [← bounded_terms wrap program key bound, List.getElem?_map]
  · exact (bounded_same _ _ (fun size => (family_terms wrap program size key).2) bound).2


end MicroCFTA.KeyedNaryMass
