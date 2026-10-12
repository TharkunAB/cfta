import MicroCFTA.RecursiveJoinComposition

/-!
# Simultaneous recursive families with heterogeneous grouped joins

Local compilation laws compose through arbitrary nested joins and choices.
The size induction derives the complete family relation. No whole-family
projection, sampler, or guard correspondence is a premise.
-/
namespace MicroCFTA.RecursiveJoinFamily
open Language GeneratorCombinators RecursiveJoinComposition
open KeyedNaryAlignment (EngineTerm)
open RecursiveJoinMass (Projects projects_decode projects_ranked)

/-- Each value key executes its independently lowered body. -/
def valueProgram (program : Key → Body Key Root Symbol Root) : Key → KeyedSource.Recipe Key Root Root :=
  fun key => (program key).value

/-- The private term program adds the exact source key and family boundary. -/
def termProgram (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :
    Key → KeyedSource.Recipe Key (EngineTerm Symbol) (EngineTerm Symbol) :=
  fun key => .map (KeyedTermBoundary.atKeyTerm (code key)) (program key).term

/-- The correlated program preserves the same private boundary at each key. -/
def pairedProgram (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :
    Key → KeyedSource.Recipe Key (Root × EngineTerm Symbol) (Root × EngineTerm Symbol) :=
  fun key => .map (fun entry => (entry.1, KeyedTermBoundary.atKeyTerm (code key) entry.2)) (program key).paired

/-- The simultaneous recursive knot retains every value, mass, and replay rank. -/
theorem family_values (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (size : Nat) (key : Key) :
    Projects Prod.fst (KeyedSource.family (pairedProgram code program) size key)
      (KeyedSource.family (valueProgram program) size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.family, KeyedSource.family]
      have body := (program key).values
        (fun childKey childSize => if childSize < size then KeyedSource.family (pairedProgram code program) childSize childKey else GroupedRecord.empty)
        (fun childKey childSize => if childSize < size then KeyedSource.family (valueProgram program) childSize childKey else GroupedRecord.empty)
        (by
          intro childKey childSize
          split
          next smaller => exact ih childSize smaller childKey
          next => exact projects_empty _) size
      refine ⟨KeyedTermMass.map_left_group _ _ _ body.1, ?_⟩
      simpa only [pairedProgram, valueProgram, KeyedSource.record, GroupedRecord.map,
        SamplerReplay.mapRecord, Decoder.values, List.map_map, Function.comp_def, dite_eq_ite] using body.2

/-- The independently tied term family retains each exact private tree and rank. -/
theorem family_terms (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (size : Nat) (key : Key) :
    Projects Prod.snd (KeyedSource.family (pairedProgram code program) size key)
      (KeyedSource.family (termProgram code program) size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.family, KeyedSource.family]
      apply projects_map_both _ _ Prod.snd _ _ Prod.snd
      · apply (program key).terms
        intro childKey childSize
        split
        next smaller => exact ih childSize smaller childKey
        next => exact projects_empty _
      · intro entry
        rfl

/-- Every value and term rank decodes the corresponding correlated member. -/
theorem decode_aligned (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (size rank : Nat) (key : Key) :
    (Decoder.decode (KeyedSource.family (pairedProgram code program) size key).members.plan rank).map Prod.fst =
      Decoder.decode (KeyedSource.family (valueProgram program) size key).members.plan rank ∧
    (Decoder.decode (KeyedSource.family (pairedProgram code program) size key).members.plan rank).map Prod.snd =
      Decoder.decode (KeyedSource.family (termProgram code program) size key).members.plan rank :=
  ⟨projects_decode _ _ _ (family_values code program size key) rank,
    projects_decode _ _ _ (family_terms code program size key) rank⟩

/-- Valid ranks produce one correlated value and term without any global completeness premise. -/
theorem rank_complete (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (size rank : Nat) (key : Key)
    (within : rank < Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan) :
    ∃ value term,
      Decoder.decode (KeyedSource.family (pairedProgram code program) size key).members.plan rank = some (value, term) ∧
      Decoder.decode (KeyedSource.family (valueProgram program) size key).members.plan rank = some value ∧
      Decoder.decode (KeyedSource.family (termProgram code program) size key).members.plan rank = some term := by
  obtain ⟨⟨value, term⟩, selected⟩ := Decoder.decode_exists _ rank ((family_values code program size key).1.2.1 ▸ within)
  refine ⟨value, term, selected, ?_, ?_⟩
  · simpa [selected] using (decode_aligned code program size rank key).1.symm
  · simpa [selected] using (decode_aligned code program size rank key).2.symm

/-- Ranked value sampling is the exact projection of the correlated family sampler. -/
theorem ranked_values (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (size : Nat) (key : Key) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (KeyedSource.family (pairedProgram code program) size key).members.sampling.ranked =
      (KeyedSource.family (valueProgram program) size key).members.sampling.ranked :=
  projects_ranked _ _ _ (family_values code program size key)
    (KeyedSource.family_valid _ size key) (KeyedSource.family_valid _ size key)

/-- Ranked term sampling retains the exact same mass at every shared source rank. -/
theorem ranked_terms (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (size : Nat) (key : Key) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (KeyedSource.family (pairedProgram code program) size key).members.sampling.ranked =
      (KeyedSource.family (termProgram code program) size key).members.sampling.ranked :=
  projects_ranked _ _ _ (family_terms code program size key)
    (KeyedSource.family_valid _ size key) (KeyedSource.family_valid _ size key)

/-- Every index supplies exactly the same source program to minimum discovery. -/
theorem minimum_programs (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :
    KeyedSource.minimumProgram (pairedProgram code program) = KeyedSource.minimumProgram (valueProgram program) ∧
    KeyedSource.minimumProgram (termProgram code program) = KeyedSource.minimumProgram (valueProgram program) := by
  constructor <;> funext key
  · exact (program key).minimum.1
  · exact (program key).minimum.2

/-- All three simultaneous knots use the same discovered key minima. -/
theorem minima_equal (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :
    KeyedSource.minima keys complete (pairedProgram code program) = KeyedSource.minima keys complete (valueProgram program) ∧
    KeyedSource.minima keys complete (termProgram code program) = KeyedSource.minima keys complete (valueProgram program) := by
  simp [KeyedSource.minima, (minimum_programs code program).1, (minimum_programs code program).2]

/-- The public value guard derives both private guards through every nested join. -/
theorem family_guards (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) :
    (∀ key, KeyedSource.guarded (pairedProgram code program key)
      (KeyedSource.minima keys complete (pairedProgram code program)) = true) ∧
    (∀ key, KeyedSource.guarded (termProgram code program key)
      (KeyedSource.minima keys complete (termProgram code program)) = true) := by
  constructor <;> intro key
  · change KeyedSource.guarded (program key).paired _ = true
    rw [(minima_equal keys complete code program).1, (program key).guards _ |>.1]
    exact accepted key
  · change KeyedSource.guarded (program key).term _ = true
    rw [(minima_equal keys complete code program).2, (program key).guards _ |>.2]
    exact accepted key

/-- Guarded composite bodies generate exactly their independent finite source derivations. -/
theorem paired_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true)
    (size : Nat) (key : Key) (value : Root) (term : EngineTerm Symbol) :
    (value, term) ∈ Decoder.values (KeyedSource.family (pairedProgram code program) size key).members.plan ↔
      KeyedSource.Derives (pairedProgram code program) (pairedProgram code program key) (value, term) size :=
  KeyedSource.family_exact keys complete _ (family_guards keys complete code program accepted).1 size key _

/-- Every accepted composite body satisfies its untruncated source record equation. -/
theorem paired_knot (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    GroupedMergeAssociativity.Fields (KeyedSource.family (pairedProgram code program) size key)
      (GroupedRecord.map (fun entry => (entry.1, KeyedTermBoundary.atKeyTerm (code key) entry.2))
        (KeyedSource.record (program key).paired
          (fun childKey childSize => KeyedSource.family (pairedProgram code program) childSize childKey) size)) :=
  KeyedNarySource.family_fields keys complete _ (family_guards keys complete code program accepted).1 size key

/-- The independent value family satisfies the complete source count, mass, and sampler equation. -/
theorem value_knot (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    GroupedMergeAssociativity.Fields (KeyedSource.family (valueProgram program) size key)
      (KeyedSource.record (program key).value
        (fun childKey childSize => KeyedSource.family (valueProgram program) childSize childKey) size) :=
  KeyedNarySource.family_fields keys complete _ accepted size key

/-- The independent term family satisfies the source record equation with its exact key wrapper. -/
theorem term_knot (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    GroupedMergeAssociativity.Fields (KeyedSource.family (termProgram code program) size key)
      (GroupedRecord.map (KeyedTermBoundary.atKeyTerm (code key))
        (KeyedSource.record (program key).term
          (fun childKey childSize => KeyedSource.family (termProgram code program) childSize childKey) size)) :=
  KeyedNarySource.family_fields keys complete _ (family_guards keys complete code program accepted).2 size key

/-- Count-weighted size bounds retain every user value and global replay probability. -/
theorem bounded_ranked_values (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (key : Key) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram code program) size key) bound).sampling.ranked =
      (GroupedRecord.bounded (fun size => KeyedSource.family (valueProgram program) size key) bound).sampling.ranked := by
  apply RecursiveRankMass.ranked_projection Prod.fst _ _ _ _
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
  · intro rank
    rw [Decoder.decode_correct, Decoder.decode_correct, ← List.getElem?_map]
    congr 1
    simp only [GroupedRecord.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
      SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap]
    congr 1
    funext size
    exact (family_values code program size key).2.symm
  · exact (RecursiveRankMass.bounded_same _ _ (fun size => (family_values code program size key).1.2) bound).2

/-- Count-weighted size bounds retain each complete private term and its global replay probability. -/
theorem bounded_ranked_terms (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (key : Key) (bound : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2))
      (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram code program) size key) bound).sampling.ranked =
      (GroupedRecord.bounded (fun size => KeyedSource.family (termProgram code program) size key) bound).sampling.ranked := by
  apply RecursiveRankMass.ranked_projection Prod.snd _ _ _ _
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid _ size key) bound).1.2
  · intro rank
    rw [Decoder.decode_correct, Decoder.decode_correct, ← List.getElem?_map]
    congr 1
    simp only [GroupedRecord.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
      SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap]
    congr 1
    funext size
    exact (family_terms code program size key).2.symm
  · exact (RecursiveRankMass.bounded_same _ _ (fun size => (family_terms code program size key).1.2) bound).2

end MicroCFTA.RecursiveJoinFamily
