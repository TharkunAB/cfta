import MicroCFTA.SourceSizedFiniteKeysDispatchGate
import MicroCFTA.SourceSizedFiniteKeysTrim

/-!
# Original raw-row dispatch scans

Finite-key restriction retains every raw constraint. The all-row plain scan
and trimmed residual scan therefore have the same exact Boolean result.
The trim equality is derived from actual productivity and reachability rounds.
-/
namespace MicroCFTA.SourceSizedFiniteKeysDispatch
open Language SourceSizedDecided SourceSizedFiniteKeys SourceSizedDispatcher SourceSizedPreprocessing
open SourceObservations SourceSymbolicIndex SourceDenseRows

variable {State : Type} [DecidableEq State] [Ord State] [DecidableEq Formula]
  (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- The source all-row constraint scan is unchanged by finite-key restriction. -/
theorem plain_eq : plainCheck (lookup table) (keys table) =
    plainCheck (input table root valid).rows (input table root valid).states := by
  have mapped : (keys table).attach.map Subtype.val = keys table := by simp
  unfold plainCheck
  conv => lhs; rw [← mapped]
  simp only [List.all_map, Function.comp_def]
  apply congrArg (fun predicate => (keys table).attach.all predicate)
  funext state
  rw [← rows_readback table (validated_closed table root valid) state]
  simp only [List.all_map]
  rfl

/-- The source trimmed residual scan retains the original constraint payload and every branch result. -/
theorem residual_eq : residualCheck (lookup table) (keys table) root =
    residualCheck (input table root valid).rows (input table root valid).states (input table root valid).root := by
  have mapped : (keys table).attach.map Subtype.val = keys table := by simp
  unfold residualCheck
  conv => lhs; arg 1; rw [← mapped]
  simp only [List.all_map, Function.comp_def]
  apply congrArg (fun predicate => (keys table).attach.all predicate)
  funext state
  have rows := SourceSizedFiniteKeysTrim.trimmedRows_readback table (validated_closed table root valid)
    (input table root valid).root state
  change (SourceSizedTrimGuards.trimmedRows (input table root valid).rows (input table root valid).states
    (input table root valid).root state).map forget =
    SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state.val at rows
  rw [← rows]
  simp only [List.all_map]
  rfl

/-- The source any-residual error scan is also identical on the original map keys. -/
theorem residual_error_eq : SourceSizedTrimGuards.residualScan (lookup table) (keys table) root =
    SourceSizedTrimGuards.residualScan (input table root valid).rows (input table root valid).states (input table root valid).root := by
  have checks := residual_eq table root valid
  simp only [residualCheck_eq_not_scan] at checks
  simpa using congrArg Bool.not checks

end MicroCFTA.SourceSizedFiniteKeysDispatch
