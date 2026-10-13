import MicroCFTA.SourceSizedBoundedSampling
import MicroCFTA.SamplerReplay

/-!
# Sampled global ranks of the distinct Sized prefix

Each class uses its public ordered terms as a uniform source record. The
existing bounded sampler applies the class offsets. Its sampled global rank
therefore decodes to the same term in the public size-major prefix. Distinct
prefix terms make the reverse lookup recover that exact sampled rank.
-/

namespace MicroCFTA.SourceSizedSamplerReplay

open Language RecursiveSize Probability SourceSizedDecided SourceSizedDispatcher
open SourceSizedPreprocessing SourceGuards SourceObservations SourceSymbolicIndex

/-- One exact class record retains the public order and one ticket per distinct term. -/
def classRecord (api : Api Symbol) (size : Nat) : SamplerReplay.Record (Term Symbol) :=
  SamplerReplay.source (counting (api.terms size))

/-- The class plan has precisely the public term sequence. -/
theorem class_values (api : Api Symbol) (size : Nat) :
    Decoder.values (classRecord api size).plan = api.terms size := by
  simp [classRecord, SamplerReplay.source, Decoder.values, counting, List.map_map, Function.comp_def]

/-- The source bounded decoder indexes the exact public prefix. -/
theorem bounded_decode (api : Api Symbol) (bound rank : Nat) :
    Decoder.decode (SamplerReplay.boundedRecord (classRecord api) bound).plan rank =
      (SourceSizedQueries.through (fun size : Nat => api.terms size) bound)[rank]? := by
  rw [SamplerReplay.bounded_decode, Decoder.decode_correct]
  simp [PlanVariants.erase, Decoder.values, class_values, SourceSizedQueries.through]

/-- Every sampled global rank retrieves its accompanying term from the public prefix. -/
theorem sampled_replay (api : Api Symbol) (bound : Nat)
    (entry : Rat × Nat × Term Symbol)
    (sampled : entry ∈ (SamplerReplay.boundedRecord (classRecord api) bound).sampling.ranked) :
    (SourceSizedQueries.through (fun size : Nat => api.terms size) bound)[entry.2.1]? =
      some entry.2.2 := by
  rw [← bounded_decode]
  exact (SamplerReplay.bounded_coherent (classRecord api) bound
    (fun size => SamplerReplay.source_coherent (counting (api.terms size)))).2 entry sampled

/-- The source sampler's value and rank fields are normalized whenever the bounded class is nonempty. -/
theorem sampled_probability (api : Api Symbol) (bound : Nat)
    (nonempty : 0 < Decoder.count (SamplerReplay.boundedRecord (classRecord api) bound).plan) :
    IsProbability (SamplerReplay.boundedRecord (classRecord api) bound).sampling.values ∧
      IsProbability (SamplerReplay.boundedRecord (classRecord api) bound).sampling.ranked := by
  apply (SamplerReplay.bounded_live (classRecord api) bound ?_).2.2 nonempty
  intro size
  apply SamplerReplay.source_live
  intro entry member
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp member
  exact show (0 : Rat) < 1 by decide

variable [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
  (input : Input State (Label Formula) (Constraint Formula))
  (api : Api (Label Formula)) (success : publicSized input = .ok api)

include success

/-- Reverse lookup recovers the global sampled rank because the public prefix has no duplicates. -/
theorem sampled_rank_inverse (bound : Nat) (entry : Rat × Nat × Term (Label Formula))
    (sampled : entry ∈ (SamplerReplay.boundedRecord (classRecord api) bound).sampling.ranked) :
    (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).idxOf entry.2.2 = entry.2.1 := by
  obtain ⟨within, found⟩ := List.getElem?_eq_some_iff.mp (sampled_replay api bound entry sampled)
  rw [← found]
  exact (SourceSizedPublicContracts.enumeration_nodup input api success bound).idxOf_getElem _ within

end MicroCFTA.SourceSizedSamplerReplay
