import MicroCFTA.MergedColdMergeStability
import MicroCFTA.MergedColdMergeBounds

/-!
# Facts along completed cold maps

Every callback uses the actual state from its preceding callback. The
returned certificate retains input/output positions and later availability.
-/
namespace MicroCFTA.MergedColdMergeMapFacts
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge Language

/-- Successful ordered maps compose source facts and preserve positional output certificates. -/
theorem map_valid (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (post : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Extension before after → ∀ request result, post before request result → post after request result)
    (checked : ∀ request before result after, Facts before → Prepared before → pre before request →
      call request before = .done result after → Extension before after ∧ post after request result)
    (requests : List Request) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (inputs : ∀ request ∈ requests, pre before request) (results : List Output) (after : State Symbol Guard)
    (done : MergedColdMerge.map call requests before = .done results after) :
    Extension before after ∧ All₂ (post after) requests results := by
  induction requests generalizing before results after with
  | nil =>
      have equal : [] = results ∧ before = after := by simpa [MergedColdMerge.map, MergedColdMerge.pure] using done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨.refl before facts prepared, .nil⟩
  | cons request rest ih =>
      cases first : call request before with
      | failed => simp [MergedColdMerge.map, MergedColdMerge.bind, first, Result.bind] at done
      | done result middle =>
          obtain ⟨extension, valid⟩ := checked request before result middle facts prepared (inputs request List.mem_cons_self) first
          cases tail : MergedColdMerge.map call rest middle with
          | failed => simp [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind] at done
          | done remaining final =>
              have equal : result :: remaining = results ∧ final = after := by
                simpa [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind, MergedColdMerge.pure] using done
              rcases equal with ⟨rfl, rfl⟩
              obtain ⟨later, related⟩ := ih middle extension.facts extension.prepared
                (fun value member => preGrows before middle extension value (inputs value (List.mem_cons_of_mem _ member)))
                remaining final tail
              exact ⟨extension.trans later, .cons (postGrows middle final later request result valid) related⟩

/-- A recursive callback retains actual cache facts and its returned source record. -/
def ValueCallValid (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before result after, Facts before → Prepared before → Available before value →
    call value before = .done result after → Extension before after ∧ Available after result

/-- Mapping a valid recursive callback preserves all returned records in the final cache. -/
theorem values_valid (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid call)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (inputs : Values before values) (results : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : MergedColdMerge.map call values before = .done results after) :
    Extension before after ∧ Values after results := by
  obtain ⟨extension, related⟩ := map_valid call Available (fun state _ result => Available state result)
    (fun _ _ extension value available => extension.available value available)
    (fun _ _ extension _ value available => extension.available value available)
    checked values before facts prepared inputs results after done
  exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩

/-- The actual recursive worker derives the callback certificate at every successful fuel choice. -/
theorem worker_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    ValueCallValid (worker grouping clear top ordinary comparison) := by
  intro value before result after facts prepared available done
  exact MergedColdMergeStability.successful_verified grouping groupsCorrect clear top value before facts prepared
    available ordinary comparison result after done

end MicroCFTA.MergedColdMergeMapFacts
