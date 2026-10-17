import MicroCFTA.SourceCurrentInitialSelectionForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SelectionForecastCheck
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentInitialSelectionForecast
open SourceEqualityClassOrder (Record)
private def record : Record := ⟨.branch [(0, .terminal), (1, .terminal)], [[0], [1]]⟩
private def original := [record, record]

/-- Two equal records give four positional choices, including two equal singleton outputs. -/
theorem positional_duplicates :
    selections original = [[], [record], [record], original] ∧
    (selections original).length = 4 ∧
    [record].Sublist original ∧ original.Sublist original := by
  refine ⟨rfl, rfl, ?_, .refl _⟩
  exact .cons_cons record (.cons record .slnil)

/-- One initial join bounds Required and Class execution for all four positional choices. -/
theorem all_initial_choices (count : Nat) (entry : Profile) :
    ∀ kept ∈ selections original,
      kept.Sublist original ∧
      Le (SourceCurrentConstrainedCapRequiredInitialNumeric.forecast
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count entry)
        (requiredProfile original count entry) ∧
      SourceCurrentConstrainedCapRequiredInitialNumeric.workerFuel
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) ≤ requiredWorker original ∧
      SourceCurrentConstrainedCapRequiredInitialNumeric.readerFuel
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count entry ≤ requiredReader original count entry ∧
      Le (SourceCurrentConstrainedCapClassForecast.foldProfile kept count entry)
        (SourceCurrentConstrainedCapClassForecast.foldProfile original count entry) ∧
      SourceCurrentConstrainedCapClassForecast.foldFuel kept count entry ≤
        SourceCurrentConstrainedCapClassForecast.foldFuel original count entry := by
  intro kept included
  have selected := selection_sublist included
  exact ⟨selected, required_selected selected count entry, required_worker_selected selected,
    required_reader_selected selected count entry, class_profile_selected selected count entry,
    class_fuel_selected selected count entry⟩

end MicroCFTA.SelectionForecastCheck

#check @MicroCFTA.SelectionForecastCheck.positional_duplicates
#print axioms MicroCFTA.SelectionForecastCheck.positional_duplicates
#check @MicroCFTA.SelectionForecastCheck.all_initial_choices
#print axioms MicroCFTA.SelectionForecastCheck.all_initial_choices
