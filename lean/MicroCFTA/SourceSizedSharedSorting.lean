import MicroCFTA.SourceSizedDeterminizationTableInput

/-!
# Shared canonical sorting across query roots

The source sorts every original row once. Canonical refinement does not
read the initial state. A validated table therefore uses the same sort
at every declared query state. The determinized table has this property
as well. No per-query validation or sort result is supplied by a caller.
-/
namespace MicroCFTA.SourceSizedSharedSorting
open Language SourceSizedFiniteKeys SourceSizedDecided Std

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Initial validation derives validation at every other declared state. -/
theorem reroot_valid (table : Table State Symbol Payload) (initial root : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table) :
    SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)) :=
  SourceSizedStructuralKeys.validation_of_closed table root present
    (SourceSizedStructuralKeys.validated_closed table initial success)

/-- Canonical refinement reads all rows and does not read the initial state. -/
theorem graph_root_independent (table : Table State Symbol Payload) (first second : State)
    (firstValid : SourceFTAValidation.validateRows first (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (secondValid : SourceFTAValidation.validateRows second (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    SourceSizedPreprocessing.graph (SourceSizedStructuralKeys.input table first firstValid) =
      SourceSizedPreprocessing.graph (SourceSizedStructuralKeys.input table second secondValid) := rfl

variable [DecidableEq Symbol] [Ord Symbol]

/-- The shared original-row sort is identical at every valid root. -/
theorem sorted_root_independent (table : Table State Symbol Payload) (first second : State)
    (firstValid : SourceFTAValidation.validateRows first (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (secondValid : SourceFTAValidation.validateRows second (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    SourceSizedStructuralKeys.nativeSorted table first firstValid =
      SourceSizedStructuralKeys.nativeSorted table second secondValid := rfl

variable [TransOrd State] [LawfulEqOrd State] [Ord (Sum State (List State))]

/-- Queries use the determinized sort built at the original initial state. -/
theorem determinized_root_independent (limit : Int) (table : Table State Symbol Payload)
    (first second : State)
    (firstValid : SourceFTAValidation.validateRows first (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (secondValid : SourceFTAValidation.validateRows second (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (known : List (List State))
    (choices : List (SourceSizedDeterminizationKernel.Choice State Symbol))
    (returned : SourceSizedDeterminizationTableInput.compile limit table = .ready known choices) :
    SourceSizedDeterminizationTableInput.sortedRows limit table first firstValid known choices returned =
      SourceSizedDeterminizationTableInput.sortedRows limit table second secondValid known choices returned := rfl

end MicroCFTA.SourceSizedSharedSorting
