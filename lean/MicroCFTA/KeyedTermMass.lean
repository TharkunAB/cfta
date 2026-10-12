import MicroCFTA.KeyedTermAlignment
import MicroCFTA.RecursiveRankMass

/-!
# Key masses and ranked probabilities of typed mutual families

The comparison retains both unnormalized key mass and the conditional mass
of each replay rank. Group choice uses key masses; rank offsets use counts.
-/
namespace MicroCFTA.KeyedTermMass
open Language GeneratorCombinators Probability SamplerReplay KeyedTermAlignment
open RecursiveRankMass (Related rankMass Same map_left map_right apply_same empty_same ranked_projection bounded_same)

/-- Different value types retain the same key mass, count, and complete ordered rank law. -/
def SameGroup (left : GroupedRecord.Group α) (right : GroupedRecord.Group β) : Prop :=
  left.mass = right.mass ∧ Same left.members right.members

/-- Mapping a grouped value preserves both mass scales and every replay rank. -/
theorem map_left_group (transform : α → β) (left : GroupedRecord.Group α)
    (right : GroupedRecord.Group γ) (same : SameGroup left right) :
    SameGroup (GroupedRecord.map transform left) right :=
  ⟨same.1, map_left _ _ _ same.2⟩

theorem map_right_group (transform : β → γ) (left : GroupedRecord.Group α)
    (right : GroupedRecord.Group β) (same : SameGroup left right) :
    SameGroup left (GroupedRecord.map transform right) :=
  ⟨same.1, map_right _ _ _ same.2⟩

/-- Counted source leaves derive their key mass from their common count. -/
theorem counted_same (left : Record α) (right : Record β) (same : Same left right) :
    SameGroup (GroupedRecord.counted left) (GroupedRecord.counted right) :=
  ⟨congrArg (fun count : Nat => (count : Rat)) same.1, same⟩

/-- A retained leaf keeps its declared mass in precisely the same live classes. -/
theorem retained_same (mass : Rat) (left : Record α) (right : Record β) (same : Same left right) :
    SameGroup (GroupedRecord.retained mass left) (GroupedRecord.retained mass right) := by
  refine ⟨?_, same⟩
  simp [GroupedRecord.retained, same.1]

/-- Grouped products multiply the same masses and apply the same mixed-radix rank law. -/
theorem apply_group (leftFunctions : GroupedRecord.Group (α → β)) (leftArguments : GroupedRecord.Group α)
    (rightFunctions : GroupedRecord.Group (γ → δ)) (rightArguments : GroupedRecord.Group γ)
    (functions : SameGroup leftFunctions rightFunctions) (arguments : SameGroup leftArguments rightArguments) :
    SameGroup (GroupedRecord.apply leftFunctions leftArguments) (GroupedRecord.apply rightFunctions rightArguments) :=
  ⟨by simp [GroupedRecord.apply, functions.1, arguments.1], apply_same _ _ _ _ functions.2 arguments.2⟩

/-- Ordered same-key choice preserves declared key masses as well as conditional rank probabilities. -/
theorem merge_same (left : List (GroupedRecord.Group α)) (right : List (GroupedRecord.Group β))
    (same : Related SameGroup left right) : SameGroup (GroupedRecord.merge left) (GroupedRecord.merge right) := by
  constructor
  · change GroupedRecord.massSum left = GroupedRecord.massSum right
    induction same with
    | nil => rfl
    | cons related remaining ih => simp only [GroupedRecord.massSum]; rw [related.1, ih]
  · constructor
    · rw [GroupedRecord.merge_count, GroupedRecord.merge_count]
      induction same with
      | nil => rfl
      | cons related remaining ih => simp only [GroupedRecord.countSum]; rw [related.2.1, ih]
    · change rankMass (manyRecord _) = rankMass (manyRecord _)
      rw [RecursiveRankMass.many_rankMass, RecursiveRankMass.many_rankMass]
      congr 1
      apply RecursiveRankMass.rows_same
      induction same with
      | nil => exact .nil
      | cons related remaining ih => exact .cons related ih

/-- Empty classes agree even when the two compilers have different value types. -/
theorem empty_group : SameGroup (GroupedRecord.empty : GroupedRecord.Group α)
    (GroupedRecord.empty : GroupedRecord.Group β) := ⟨rfl, empty_same⟩

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
  | choice left right ihl ihr =>
      exact merge_same _ _ (.cons (map_left_group _ _ _ (ihl size)) (.cons (map_left_group _ _ _ (ihr size)) .nil))
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
  | choice left right ihl ihr =>
      exact merge_same _ _ (.cons (map_right_group _ _ _ (map_left_group _ _ _ (ihl size)))
        (.cons (map_right_group _ _ _ (map_left_group _ _ _ (ihr size))) .nil))
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

/-- Mutually recursive retained masses stay nonuniform after two cross-key occurrences. -/
example : (KeyedSource.family (sourcePairedProgram twoKeyPosition twoKeyExample) 2 false).mass = 10 ∧
    rankMass (KeyedSource.family (sourcePairedProgram twoKeyPosition twoKeyExample) 2 false).members =
      [(9 / 10, 0), (1 / 10, 1)] := by cbv

end MicroCFTA.KeyedTermMass
