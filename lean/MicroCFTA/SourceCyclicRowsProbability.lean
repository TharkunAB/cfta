import MicroCFTA.SourceCyclicRowsExecution
import MicroCFTA.SourcePmfQuery
import MicroCFTA.RecursiveRecord

/-!
# Exact sampling and PMFs of the current cyclic row compiler

The cyclic fromAutomaton branch constructs uniformSampleIndex from its
compiled count and selector. Exact backend ranks give one reciprocal-count
share to every class position. Successful source prechecks derive distinct
terms, so those shares are also uniform term probabilities. Empty classes
return an empty public PMF before the sampler is read.
-/

namespace MicroCFTA.SourceCyclicRowsProbability

open Language Probability Sampler RecursiveSize SizedRank
open SourceDenseRows SourceGuards SourceObservations

/-- The actual Exact backend lists each valid integer rank with its uniform share. -/
def exactRanks (count : Nat) : Distribution Nat :=
  (List.range count).map fun rank => (1 / (count : Rat), rank)

/-- Exact backend enumeration derives the mathematical uniform rank law. -/
theorem exactRanks_uniform (count : Nat) : exactRanks count = uniformRanks count := by
  unfold uniformRanks normalize
  rw [total_counting, List.length_range]
  simp [exactRanks, counting, scale, List.map_map, Function.comp_def, Rat.div_def]

/-- The source singleton shortcut precedes its ordinary rank-selection branch. -/
def exactUniform (count : Nat) (valueAt : Nat → Value) : ExactSampler Value :=
  if count = 1 then ⟨[(1, valueAt 0)], [(1, (0, valueAt 0))]⟩
  else ⟨Probability.map valueAt (exactRanks count),
    Probability.map (fun rank => (rank, valueAt rank)) (exactRanks count)⟩

/-- The actual Exact singleton and rank branches construct the same two sampler fields. -/
theorem exactUniform_uniform (count : Nat) (valueAt : Nat → Value) :
    exactUniform count valueAt = uniformSampler count valueAt := by
  by_cases singleton : count = 1
  · subst count
    obtain ⟨values, ranked⟩ := uniformSampler_one valueAt
    cases found : uniformSampler 1 valueAt with
    | mk v r =>
      simp only [found] at values ranked
      simp [exactUniform, values, ranked]
  · simp [exactUniform, singleton, exactRanks_uniform, uniformSampler]

/-- The source cyclic record reads its count and sampler from one compiled class plan. -/
def record (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) :
    SourcePmfQuery.Recursive (Term Symbol) where
  count size := (countAt A size.toNat root : Int)
  sampling size := (RecursiveRecord.classRecord A root size.toNat fallback).sampling

/-- Both actual Exact sampler fields use the count-table selector at the same class rank. -/
theorem sampler_fields (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) :
    (record A root fallback).sampling size = exactUniform (countAt A size.toNat root)
      (fun rank => (replayPosition A root ⟨size.toNat, rank⟩).getD fallback) := by
  rw [exactUniform_uniform]
  simp [record, RecursiveRecord.classRecord, RecursiveRecord.uniformRecord, Decoder.count_normalize, count_compileAt,
    replayPosition]

/-- The actual class sampler has precisely the compiled ordered member distribution. -/
theorem sampler_values (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) :
    ((record A root fallback).sampling size).values = normalize (counting (RecursiveSize.enumerate A size.toNat root)) :=
  RecursiveRecord.class_distribution A root size.toNat fallback

/-- Public recursive PMF dispatch reads this derived distribution, including empty classes. -/
theorem pmf_rows [DecidableEq Symbol] [Ord (Term Symbol)]
    (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) :
    SourcePmfQuery.recursiveAtSize (record A root fallback) size =
      SourcePmfAggregation.pmf (normalize (counting (RecursiveSize.enumerate A size.toNat root))) := by
  unfold SourcePmfQuery.recursiveAtSize
  split
  next empty =>
    have zero : countAt A size.toNat root = 0 := by simpa [record] using empty
    have absent : RecursiveSize.enumerate A size.toNat root = [] :=
      List.length_eq_zero_iff.mp (by rw [← countAt_correct, zero])
    simp [absent, SourcePmfAggregation.pmf, SourcePmfAggregation.aggregate, SourcePmfAggregation.fromList,
      normalize, counting, total, scale]
  next live => rw [sampler_values]

/-- Compilation and recursive query preparation precede the actual size PMF observer. -/
theorem public_pmf [DecidableEq Symbol] [Ord (Term Symbol)]
    (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) :
    SourcePmfQuery.pmfAtSize (SourceError := Error) (.cyclic (.ok (.ok (record A root fallback)))) size =
      .ok (SourcePmfAggregation.pmf (normalize (counting (RecursiveSize.enumerate A size.toNat root)))) := by
  simp only [SourcePmfQuery.pmfAtSize, Bind.bind, Except.bind, pmf_rows]
  rfl

/-- Nonpositive tree-node sizes return an empty PMF and do not read the selector. -/
theorem pmf_nonpositive [DecidableEq Symbol] [Ord (Term Symbol)]
    (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) (nonpositive : size ≤ 0) :
    SourcePmfQuery.recursiveAtSize (record A root fallback) size = [] := by
  rw [pmf_rows, Int.toNat_of_nonpos nonpositive, enumerate_zero]
  simp [SourcePmfAggregation.pmf, SourcePmfAggregation.aggregate, SourcePmfAggregation.fromList,
    normalize, counting, total, scale]

/-- Every output event receives exactly its class-position count divided by the class cardinality. -/
theorem pmf_event [DecidableEq Symbol] [Ord (Term Symbol)]
    (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int) (event : Term Symbol → Bool) :
    eventMass event ((SourcePmfQuery.recursiveAtSize (record A root fallback) size).map Prod.swap) =
      ((RecursiveSize.enumerate A size.toNat root).countP event : Rat) / (countAt A size.toNat root : Rat) := by
  rw [pmf_rows, SourcePmfAggregation.pmf_distribution, SourcePmfAggregation.event_aggregate,
    uniform_event_probability, ← countAt_correct]

/-- Positive compiled cardinality derives normalization of both samplers and the public PMF. -/
theorem probability [DecidableEq Symbol] [Ord (Term Symbol)]
    (A : Automaton State Symbol) (root : State) (fallback : Term Symbol) (size : Int)
    (live : 0 < countAt A size.toNat root) :
    IsProbability ((record A root fallback).sampling size).values ∧
      IsProbability ((record A root fallback).sampling size).ranked ∧
      IsProbability ((SourcePmfQuery.recursiveAtSize (record A root fallback) size).map Prod.swap) := by
  have valid := (RecursiveRecord.class_live A root size.toNat fallback).2.2
    (by rwa [RecursiveRecord.class_count])
  refine ⟨valid.1, valid.2, ?_⟩
  exact SourcePmfQuery.recursive_probability _ size (by simpa [record] using live) valid.1

variable {State : Type} {keys : List State}
  [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
  (formulas : Formulas Formula) (solver : Entailment Formula) (input : SourceCyclicRows.Input keys Formula)
  (order : Label Formula → Key) (output : Automaton (Member keys) (Label Formula))
  (success : SourceCyclicRows.compile formulas solver input order = some (.ok output))

include success

/-- The sampler support is exactly the original guarded language at the signed node size. -/
theorem class_members (size : Int) (term : Term (Label Formula)) :
    term ∈ RecursiveSize.enumerate output size.toNat input.root ↔
      Accepts (SourceCyclicRows.original formulas solver input) input.root term ∧ (nodeSize term : Int) = size := by
  obtain ⟨_, _, language, _, _⟩ := SourceCyclicRows.class_correct formulas solver input order output success size.toNat
  rw [language]
  have positive := nodeSize_pos term
  constructor <;> rintro ⟨accepted, sized⟩ <;> exact ⟨accepted, by omega⟩

/-- Aggregated public PMF keys are exactly the distinct original terms of this signed size. -/
theorem pmf_keys [Ord (Term (Label Formula))] (fallback term : Term (Label Formula)) (size : Int) :
    term ∈ (SourcePmfQuery.recursiveAtSize (record output input.root fallback) size).map Prod.fst ↔
      Accepts (SourceCyclicRows.original formulas solver input) input.root term ∧ (nodeSize term : Int) = size := by
  rw [pmf_rows]
  simp only [SourcePmfAggregation.pmf, List.map_map, Function.comp_def]
  rw [SourcePmfAggregation.aggregate_keys]
  simpa [normalize, scale, counting, List.map_map, Function.comp_def] using
    class_members formulas solver input order output success size term

/-- Source prechecks derive distinct terms, so each accepted term receives one reciprocal-count share. -/
theorem term_mass [Ord (Term (Label Formula))]
    (fallback term : Term (Label Formula)) (size : Int) :
    eventMass (fun found => found == term)
      ((SourcePmfQuery.recursiveAtSize (record output input.root fallback) size).map Prod.swap) =
        @ite Rat (Accepts (SourceCyclicRows.original formulas solver input) input.root term ∧ (nodeSize term : Int) = size)
          (Classical.propDecidable _) (1 / (countAt output size.toNat input.root : Rat)) 0 := by
  classical
  rw [pmf_event, ← List.count_eq_countP]
  obtain ⟨_, unique, _, _, _⟩ := SourceCyclicRows.class_correct formulas solver input order output success size.toNat
  simp only [unique.count, class_members formulas solver input order output success size term]
  split <;> simp [Rat.div_def]

/-- Every sampled local class rank replays and is recovered by the actual table position callback. -/
theorem sampled_inverse (fallback : Term (Label Formula)) (size : Nat)
    (entry : Rat × Nat × Term (Label Formula))
    (sampled : entry ∈ ((record output input.root fallback).sampling size).ranked) :
    replayPosition output input.root ⟨size, entry.2.1⟩ = some entry.2.2 ∧
      TablePosition.positionsOf output entry.2.2 input.root = some ⟨size, entry.2.1⟩ := by
  have replay := (RecursiveRecord.class_live output input.root size fallback).1.2 entry sampled
  change replayPosition output input.root ⟨size, entry.2.1⟩ = some entry.2.2 at replay
  exact ⟨replay, (SourceCyclicRows.query_inverses formulas solver input order output success).1 _ _ |>.mpr replay⟩

/-- No positive-probability source term is missed by the independently constructed rank sampler. -/
theorem sampled_support (fallback term : Term (Label Formula)) (size : Int) :
    (∃ rank mass, 0 < mass ∧ (mass, (rank, term)) ∈ ((record output input.root fallback).sampling size).ranked) ↔
      Accepts (SourceCyclicRows.original formulas solver input) input.root term ∧ (nodeSize term : Int) = size := by
  obtain ⟨plain, _, language⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  rw [show ((record output input.root fallback).sampling size) =
    (RecursiveRecord.classRecord output input.root size.toNat fallback).sampling from rfl,
    RecursiveRecord.class_sample_exact output plain input.root size.toNat fallback term, language]
  have positive := nodeSize_pos term
  constructor <;> rintro ⟨accepted, sized⟩ <;> exact ⟨accepted, by omega⟩

end MicroCFTA.SourceCyclicRowsProbability
