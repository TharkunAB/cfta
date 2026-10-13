import MicroCFTA.SourcePmfAggregation
import MicroCFTA.SamplerReplay

/-!
# Source finite and recursive PMF queries

Finite PMFs normalize the enumerated global outcome masses. Finite size
PMFs first select occurrence ranks with the requested plan size. Recursive
size PMFs interpret that size's sampler. These are different source paths.
The public result aggregates equal values only after these operations.
-/
namespace MicroCFTA.SourcePmfQuery
open Probability SourcePmfAggregation

/-- Query failures preserve prior source errors and distinguish unsupported observations. -/
inductive Error (SourceError : Type) where
  | source (error : SourceError)
  | emptyGenerator
  | unboundedGenerator
  | cannotInspectOpaqueGenerator
  deriving DecidableEq, Repr

/-- A completed finite Static record still has a fallible outcome enumeration. -/
structure Finite (Value SourceError : Type) where
  enumerate : Except (Error SourceError) (Distribution Value)
  sizeAt : Nat → Int

/-- The recursive query worker supplies a signed count and exact class sampler. -/
structure Recursive (Value : Type) where
  count : Int → Int
  sampling : Int → Sampler.ExactSampler Value

/-- Preserve compilation failure separately from recursive-query preparation failure. -/
inductive Input (Value SourceError : Type) where
  | transparent (result : Except (Error SourceError) (Finite Value SourceError))
  | cyclic (result : Except (Error SourceError) (Except (Error SourceError) (Recursive Value)))
  | opaque

/-- The empty list and nonpositive total mass both give the source EmptyGenerator error. -/
def normalizeChecked (outcomes : Distribution Value) : Except (Error SourceError) (Distribution Value) :=
  if 0 < total outcomes then .ok (normalize outcomes) else .error .emptyGenerator

/-- Normalization succeeds precisely at positive total mass and retains source occurrence order. -/
theorem normalizeChecked_success (outcomes normalized : Distribution Value) :
    normalizeChecked (SourceError := SourceError) outcomes = .ok normalized ↔
      0 < total outcomes ∧ normalized = normalize outcomes := by
  unfold normalizeChecked
  split <;> simp_all [eq_comm]

/-- Nonpositive total mass gives the exact normalization error. -/
theorem normalizeChecked_error (outcomes : Distribution Value) :
    normalizeChecked (SourceError := SourceError) outcomes = .error .emptyGenerator ↔ total outcomes ≤ 0 := by
  simp [normalizeChecked, Rat.not_lt]

/-- A successful finite query normalizes its original masses before map aggregation. -/
def finite [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) :
    Except (Error SourceError) (List (Value × Rat)) :=
  (normalizeChecked outcomes).map SourcePmfAggregation.pmf

/-- Select original occurrence ranks by their plan sizes before duplicate-output aggregation. -/
def selected (sizeAt : Nat → Int) (size : Int) (outcomes : Distribution Value) : Distribution Value :=
  outcomes.zipIdx.filterMap fun (entry, rank) => if sizeAt rank = size then some entry else none

/-- Retain every global replay occurrence while exposing its stable rank. -/
def indexed (outcomes : Distribution Value) : Distribution (Nat × Value) :=
  outcomes.zipIdx.map fun (entry, rank) => (entry.1, (rank, entry.2))

/-- Source plan-size filtering is exact conditioning on occurrence ranks before value projection. -/
theorem selected_rank_filter (sizeAt : Nat → Int) (size : Int) (outcomes : Distribution Value) :
    selected sizeAt size outcomes = Probability.map Prod.snd
      (restrict (fun ranked => decide (sizeAt ranked.1 = size)) (indexed outcomes)) := by
  have step (entries : List ((Rat × Value) × Nat)) :
      entries.filterMap (fun (entry, rank) => if sizeAt rank = size then some entry else none) =
        Probability.map Prod.snd (restrict (fun ranked => decide (sizeAt ranked.1 = size))
          (entries.map fun (entry, rank) => (entry.1, (rank, entry.2)))) := by
    induction entries with
    | nil => rfl
    | cons first rest ih =>
        obtain ⟨⟨mass, value⟩, rank⟩ := first
        by_cases belongs : sizeAt rank = size <;>
          simp [restrict, Probability.map, belongs, ih]
  exact step outcomes.zipIdx

/-- Finite-class mass sums exactly the global occurrences whose plan size matches. -/
theorem selected_total (sizeAt : Nat → Int) (size : Int) (outcomes : Distribution Value) :
    total (selected sizeAt size outcomes) =
      eventMass (fun ranked => decide (sizeAt ranked.1 = size)) (indexed outcomes) := by
  rw [selected_rank_filter, total_map, total_restrict]

/-- Observable class events retain the original rank weights even when output values coincide. -/
theorem selected_event (sizeAt : Nat → Int) (size : Int) (outcomes : Distribution Value)
    (event : Value → Bool) : eventMass event (selected sizeAt size outcomes) =
      eventMass (fun ranked => decide (sizeAt ranked.1 = size) && event ranked.2) (indexed outcomes) := by
  rw [selected_rank_filter, eventMass_map, eventMass_restrict]
  rfl

/-- The finite size observer returns an empty PMF for absent classes. -/
def finiteAtSize [DecidableEq Value] [Ord Value] (record : Finite Value SourceError) (size : Int) :
    Except (Error SourceError) (List (Value × Rat)) :=
  if size < 0 then .ok [] else do
    let outcomes ← record.enumerate
    let chosen := selected record.sizeAt size outcomes
    if chosen.isEmpty then .ok [] else finite chosen

/-- The recursive observer does not read the sampler for a nonpositive class count. -/
def recursiveAtSize [DecidableEq Value] [Ord Value] (record : Recursive Value) (size : Int) :
    List (Value × Rat) :=
  if record.count size ≤ 0 then [] else SourcePmfAggregation.pmf (record.sampling size).values

/-- The actual public whole-generator PMF dispatch preserves source error order. -/
def pmf [DecidableEq Value] [Ord Value] : Input Value SourceError → Except (Error SourceError) (List (Value × Rat))
  | .transparent result => do
      let record ← result
      let outcomes ← record.enumerate
      finite outcomes
  | .cyclic (.error error) => .error error
  | .cyclic (.ok _) => .error .unboundedGenerator
  | .opaque => .error .cannotInspectOpaqueGenerator

/-- The actual public size PMF dispatch checks compilation before its negative-size shortcut. -/
def pmfAtSize [DecidableEq Value] [Ord Value] (input : Input Value SourceError) (size : Int) :
    Except (Error SourceError) (List (Value × Rat)) :=
  match input with
  | .transparent result => do
      let record ← result
      finiteAtSize record size
  | .cyclic result => do
      let prepared ← result
      let record ← prepared
      pure (recursiveAtSize record size)
  | .opaque => .error .cannotInspectOpaqueGenerator

/-- Successful normalized finite PMFs have exactly the original conditional event masses. -/
theorem finite_event [DecidableEq Value] [Ord Value]
    (outcomes : Distribution Value) (positive : 0 < total outcomes)
    (event : Value → Bool) :
    finite (SourceError := SourceError) outcomes = .ok (SourcePmfAggregation.pmf (normalize outcomes)) ∧
    eventMass event ((SourcePmfAggregation.pmf (normalize outcomes)).map Prod.swap) =
      eventMass event outcomes / total outcomes := by
  refine ⟨by simp [finite, normalizeChecked, positive, Except.map], ?_⟩
  rw [pmf_distribution, event_aggregate, normalize, eventMass_scale]
  simp only [Rat.div_def, Rat.mul_comm]

/-- Positive-total nonnegative finite masses yield a normalized PMF on distinct output keys. -/
theorem finite_probability [DecidableEq Value] [Ord Value]
    (outcomes : Distribution Value) (nonnegative : Nonnegative outcomes) (positive : 0 < total outcomes) :
    IsProbability ((SourcePmfAggregation.pmf (normalize outcomes)).map Prod.swap) := by
  rw [pmf_distribution]
  exact aggregate_probability _ (normalize_probability outcomes nonnegative positive)

/-- A nonempty selected finite class reports its normalized occurrence masses. -/
theorem finite_size_event [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (outcomes : Distribution Value)
    (enumerated : record.enumerate = .ok outcomes) (size : Int) (nonnegative : 0 ≤ size)
    (positive : 0 < total (selected record.sizeAt size outcomes)) :
    finiteAtSize record size =
      .ok (SourcePmfAggregation.pmf (normalize (selected record.sizeAt size outcomes))) := by
  have nonempty : selected record.sizeAt size outcomes ≠ [] := by
    intro empty
    simp [empty, total] at positive
  simp [finiteAtSize, show ¬size < 0 by omega, enumerated, nonempty, finite,
    normalizeChecked, positive, Bind.bind, Except.bind, Except.map]

/-- The public finite-size PMF is the conditional probability of global replay occurrences. -/
theorem finite_size_conditional [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (outcomes : Distribution Value)
    (enumerated : record.enumerate = .ok outcomes) (size : Int) (nonnegative : 0 ≤ size)
    (positive : 0 < total (selected record.sizeAt size outcomes)) (event : Value → Bool) :
    finiteAtSize record size = .ok (SourcePmfAggregation.pmf (normalize (selected record.sizeAt size outcomes))) ∧
      eventMass event ((SourcePmfAggregation.pmf (normalize (selected record.sizeAt size outcomes))).map Prod.swap) =
        eventMass (fun ranked => decide (record.sizeAt ranked.1 = size) && event ranked.2) (indexed outcomes) /
          eventMass (fun ranked => decide (record.sizeAt ranked.1 = size)) (indexed outcomes) := by
  refine ⟨finite_size_event record outcomes enumerated size nonnegative positive, ?_⟩
  rw [(finite_event (SourceError := SourceError) (selected record.sizeAt size outcomes) positive event).2,
    selected_total, selected_event]

/-- Every recursive PMF event is exactly the event of its independently built class sampler. -/
theorem recursive_event [DecidableEq Value] [Ord Value]
    (record : Recursive Value) (size : Int) (live : 0 < record.count size) (event : Value → Bool) :
    eventMass event ((recursiveAtSize record size).map Prod.swap) =
      eventMass event (record.sampling size).values := by
  rw [recursiveAtSize, ite_eq_right (by omega), pmf_distribution, event_aggregate]

/-- A normalized recursive class sampler gives a normalized distinct-output PMF. -/
theorem recursive_probability [DecidableEq Value] [Ord Value]
    (record : Recursive Value) (size : Int) (live : 0 < record.count size)
    (valid : IsProbability (record.sampling size).values) :
    IsProbability ((recursiveAtSize record size).map Prod.swap) := by
  rw [recursiveAtSize, ite_eq_right (by omega), pmf_distribution]
  exact aggregate_probability _ valid

/-- Negative finite sizes skip the fallible outcome enumeration after Static construction succeeds. -/
theorem negative_finite [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (size : Int) (negative : size < 0) :
    pmfAtSize (.transparent (.ok record)) size = .ok [] := by
  simp [pmfAtSize, finiteAtSize, negative, Bind.bind, Except.bind]

/-- A failed Static construction is reported before the negative-size shortcut. -/
theorem finite_error_first [DecidableEq Value] [Ord Value]
    (error : Error SourceError) (size : Int) :
    pmfAtSize (Value := Value) (.transparent (.error error)) size = .error error := rfl

/-- Whole-generator cyclic inspection does not call the recursive query preparation worker. -/
theorem cyclic_unbounded_first [DecidableEq Value] [Ord Value]
    (error : Error SourceError) :
    pmf (Value := Value) (.cyclic (.ok (.error error))) = .error .unboundedGenerator := rfl

/-- Size inspection retains the exact failure from recursive query preparation. -/
theorem cyclic_preparation_error [DecidableEq Value] [Ord Value]
    (error : Error SourceError) (size : Int) :
    pmfAtSize (Value := Value) (.cyclic (.ok (.error error))) size = .error error := rfl

/-- The public finite observer returns the exact aggregated normalized source outcomes. -/
theorem pmf_transparent [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (outcomes : Distribution Value)
    (enumerated : record.enumerate = .ok outcomes) (positive : 0 < total outcomes) :
    pmf (.transparent (.ok record)) = .ok (SourcePmfAggregation.pmf (normalize outcomes)) := by
  simp [pmf, enumerated, finite, normalizeChecked, positive, Bind.bind, Except.bind, Except.map]

/-- The public finite size observer conditions on the actual occurrence-rank plan sizes. -/
theorem pmfAtSize_transparent [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (outcomes : Distribution Value)
    (enumerated : record.enumerate = .ok outcomes) (size : Int) (nonnegative : 0 ≤ size)
    (positive : 0 < total (selected record.sizeAt size outcomes)) :
    pmfAtSize (.transparent (.ok record)) size =
      .ok (SourcePmfAggregation.pmf (normalize (selected record.sizeAt size outcomes))) :=
  finite_size_event record outcomes enumerated size nonnegative positive

/-- A public recursive query reads its class sampler after both preparation stages succeed. -/
theorem pmfAtSize_cyclic [DecidableEq Value] [Ord Value]
    (record : Recursive Value) (size : Int) (live : 0 < record.count size) :
    pmfAtSize (SourceError := SourceError) (.cyclic (.ok (.ok record))) size =
      .ok (SourcePmfAggregation.pmf (record.sampling size).values) := by
  simp [pmfAtSize, recursiveAtSize, show ¬record.count size ≤ 0 by omega, Bind.bind, Except.bind]
  rfl

/-- Count-zero classes return an empty PMF without requiring a sampler probability premise. -/
theorem pmfAtSize_cyclic_empty [DecidableEq Value] [Ord Value]
    (record : Recursive Value) (size : Int) (empty : record.count size ≤ 0) :
    pmfAtSize (SourceError := SourceError) (.cyclic (.ok (.ok record))) size = .ok [] := by
  simp [pmfAtSize, recursiveAtSize, empty, Bind.bind, Except.bind]
  rfl

/-- An absent finite size class is a successful empty PMF, unlike an empty whole-generator normalization. -/
theorem pmfAtSize_finite_empty [DecidableEq Value] [Ord Value]
    (record : Finite Value SourceError) (outcomes : Distribution Value)
    (enumerated : record.enumerate = .ok outcomes) (size : Int) (nonnegative : 0 ≤ size)
    (empty : selected record.sizeAt size outcomes = []) :
    pmfAtSize (.transparent (.ok record)) size = .ok [] := by
  simp [pmfAtSize, finiteAtSize, show ¬size < 0 by omega, enumerated, empty, Bind.bind, Except.bind]

/-- Uniform member sampling assigns each output its occurrence multiplicity divided by member count. -/
theorem uniform_output_probability [DecidableEq Value] [Ord Value]
    (values : List Value) (event : Value → Bool) :
    eventMass event ((SourcePmfAggregation.pmf (normalize (counting values))).map Prod.swap) =
      (values.countP event : Rat) / (values.length : Rat) := by
  rw [pmf_distribution, event_aggregate]
  exact uniform_event_probability event values

/-- The Exact weighted backend and normalized declared integer weights report the same PMF. -/
theorem exactWeighted_pmf [DecidableEq Value] [Ord Value] (weighted : List (Nat × Value)) :
    SourcePmfAggregation.pmf (Sampler.exactSelectWeighted weighted) =
      SourcePmfAggregation.pmf (normalize (Sampler.weightDistribution weighted)) := by
  rw [Sampler.exactSelectWeighted_correct]

/-- Compiled ticket sampling and the source PMF agree after duplicate-output aggregation. -/
theorem compiled_pmf_event [DecidableEq Value] [Ord Value]
    (outcomes : Distribution Value) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) (event : Value → Bool) :
    eventMass (fun result => result.any event)
      (Sampler.binarySampling (Sampler.groupWeighted (Sampler.integerMasses outcomes))) =
      eventMass event ((SourcePmfAggregation.pmf (normalize outcomes)).map Prod.swap) := by
  rw [pmf_distribution, event_aggregate]
  exact Sampler.compiled_rational_probability outcomes nonempty positive event

/-- Stored sampled ranks and the exact public PMF have the same observable value probabilities. -/
theorem coherent_sampler_pmf [DecidableEq Value] [Ord Value]
    (sampling : Sampler.ExactSampler Value) (coherent : Sampler.Coherent sampling) (event : Value → Bool) :
    eventMass event ((SourcePmfAggregation.pmf sampling.values).map Prod.swap) =
      eventMass (fun ranked => event ranked.2) sampling.ranked := by
  rw [pmf_distribution, event_aggregate, ← coherent, eventMass_map]
  rfl

/-- A proved finite sampler record gives a normalized public PMF with all replay occurrences aggregated. -/
theorem valid_record_pmf [DecidableEq Value] [Ord Value]
    (record : SamplerReplay.Record Value) (valid : SamplerReplay.Valid record) :
    IsProbability ((SourcePmfAggregation.pmf record.sampling.values).map Prod.swap) ∧
      ∀ event, eventMass event ((SourcePmfAggregation.pmf record.sampling.values).map Prod.swap) =
        eventMass (fun ranked => event ranked.2) record.sampling.ranked := by
  refine ⟨?_, coherent_sampler_pmf record.sampling valid.1.1⟩
  rw [pmf_distribution]
  exact aggregate_probability _ valid.2.1

end MicroCFTA.SourcePmfQuery
