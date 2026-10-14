import MicroCFTA.SourceFreshOrdinaryLiquidEntry
import MicroCFTA.SourceSizedNormalizedConstraints
import MicroCFTA.SourceSizedFiniteKeysApiLaws

/-!
# Public reference and optimized Sized queries after repaired cold conversion

Both paths use the actual validated normalized FTA. Physical open checks
and conversion errors precede Sized. The optimized dispatcher and reference
return identical complete records and residual-guard errors.
-/
namespace MicroCFTA.SourceFreshOrdinarySizedEntry
open Cache Language InternedConstructorTemplates
open SourceObservations SourceSymbolicIndex SourceSizedFiniteKeys
open SourceFreshOrdinaryLiquidEntry (rawRows queryRows)
open SourcePreparedSharedRows (encode)
open SourceColdSharedRows (Rows)
open SourceFreshOrdinaryColdSharedRows (Trace)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "C" => InternedConstructorTemplates.State Symbol Guard
local notation "V" => InternedConstructorTemplates.Value Symbol Guard
local notation "Api" => SourceSizedDispatcher.Api Symbol

/-- Conversion failures and the source residual-guard failure retain separate channels. -/
abbrev Result := Except (SourceInternedRows.ViewError Symbol) (Except Unit Api)

variable [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]

/-- Select the actual optimized dispatcher or the actual original-map reference. -/
noncomputable def queries (dispatch : Bool) (table : SourceSizedFiniteKeysPublic.LiquidTable SourceInternedRows.State)
    (root : SourceInternedRows.State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : Except Unit Api :=
  if dispatch then SourceSizedFiniteKeysDispatch.nativeSized table root valid
  else SourceSizedFiniteKeysDispatch.nativeReference table root valid

/-- Actual dispatch and reference return the same complete query record or exact residual error. -/
theorem queries_reference (dispatch : Bool) (table : SourceSizedFiniteKeysPublic.LiquidTable SourceInternedRows.State)
    (root : SourceInternedRows.State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    queries dispatch table root valid = SourceSizedFiniteKeysDispatch.nativeReference table root valid := by
  cases dispatch
  · rfl
  · change SourceSizedFiniteKeysDispatch.nativeSized table root valid = _
    rw [SourceSizedFiniteKeysDispatch.nativeSized_eq, SourceSizedFiniteKeysDispatch.nativeReference_eq,
      SourceSizedPreprocessing.publicSized_eq_reference]

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual staged execution validates cold rows before either Sized path. -/
inductive Execution (dispatch : Bool) (value : V) : C → Result → C → Prop where
  | openRoot (state : C) (isOpen : value.free ≠ []) :
      Execution dispatch value state (.error .openNode) state
  | invalid (state final : C) (rows : Rows Symbol Guard) (keys : List Nat)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
      (closed : value.free = []) (trace : Trace state (fun _ => none) [value] rows final)
      (error : FTAValidation.Error SourceInternedRows.State Symbol)
      (checked : FTAValidation.mkFTA (encode value) (interpreted (rawRows rows keys value) (fun _ _ => true)) = .error error) :
      Execution dispatch value state (.error (.invalidFTA error)) final
  | returned (state final : C) (rows : Rows Symbol Guard) (keys : List Nat)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
      (closed : value.free = []) (trace : Trace state (fun _ => none) [value] rows final)
      (checked : FTAValidation.mkFTA (encode value) (interpreted (rawRows rows keys value) (fun _ _ => true)) =
        .ok (interpreted (queryRows rows keys value) (fun _ _ => true))) :
      Execution dispatch value state
        (.ok (queries dispatch (queryRows rows keys value) (encode value)
          (normalized_validated (rawRows rows keys value) (encode value) checked))) final

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- An open root returns its conversion error and the identical constructor cache. -/
theorem Execution.open_result (dispatch : Bool) (value : V) (state final : C) (result : Result)
    (actual : Execution dispatch value state result final) (isOpen : value.free ≠ []) :
    result = .error .openNode ∧ final = state := by
  cases actual <;> simp_all

/-- Switching between reference and optimized dispatch retains every result field, error, and final cache. -/
theorem Execution.change_dispatch (dispatch other : Bool) (value : V) (state final : C) (result : Result)
    (actual : Execution dispatch value state result final) : Execution other value state result final := by
  cases actual with
  | openRoot isOpen => exact .openRoot state isOpen
  | invalid final rows keys domain closed trace error checked =>
      exact .invalid state final rows keys domain closed trace error checked
  | returned final rows keys domain closed trace checked =>
      have same : queries other (queryRows rows keys value) (encode value)
          (normalized_validated (rawRows rows keys value) (encode value) checked) =
          queries dispatch (queryRows rows keys value) (encode value)
            (normalized_validated (rawRows rows keys value) (encode value) checked) :=
        (queries_reference other _ _ _).trans (queries_reference dispatch _ _ _).symm
      rw [← same]
      exact .returned state final rows keys domain closed trace checked

end MicroCFTA.SourceFreshOrdinarySizedEntry
