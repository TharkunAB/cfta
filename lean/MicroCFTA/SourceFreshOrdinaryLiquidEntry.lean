import MicroCFTA.SourceFreshOrdinaryColdLiquid

/-!
# Public conversion followed by actual encoded bounded Sized execution

The physical free-variable check precedes traversal. Closed inputs produce
raw rows and run the actual FTA validator. Only successful validation starts
the encoded solver fold. The public result retains conversion errors,
raised solver failures, GuardUnknown, and a common complete query record.
-/
namespace MicroCFTA.SourceFreshOrdinaryLiquidEntry
open Cache Language InternedConstructorTemplates
open SourceObservations SourceSymbolicIndex SourceSizedFiniteKeys
open SolverAdapter SourceSizedLiquidProgram
open SourcePreparedSharedRows (encode)
open SourceColdSharedRows (Rows sizedTable table)
open SourceFreshOrdinaryColdSharedRows (Trace)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "C" => InternedConstructorTemplates.State Symbol Guard
local notation "V" => InternedConstructorTemplates.Value Symbol Guard
local notation "Item" => Guard × Term Symbol
local notation "Api" => SourceSizedDispatcher.Api Symbol

/-- Conversion failures, raised solver errors, Unknown, and successful queries retain separate channels. -/
abbrev Result := Except (SourceInternedRows.ViewError Symbol) (SourceSizedLiquidExecution.Outcome Item Api)

/-- The actual ascending raw cold table retains complete source constraints. -/
def rawRows (rows : Rows Symbol Guard) (keys : List Nat) (value : V) := sizedTable (table rows keys value)

/-- The FTA builder merges and sorts the raw rows before Sized reads them. -/
def queryRows (rows : Rows Symbol Guard) (keys : List Nat) (value : V) := normalized (rawRows rows keys value)

variable [Ord Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual staged execution returns before solver work on every conversion failure. -/
inductive Execution (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (bound : Int) (value : V) : C → Result → C → Prop where
  | openRoot (state : C) (isOpen : value.free ≠ []) :
      Execution given assumptions milliseconds check bound value state (.error .openNode) state
  | invalid (state final : C) (rows : Rows Symbol Guard) (keys : List Nat)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
      (closed : value.free = []) (trace : Trace state (fun _ => none) [value] rows final)
      (error : FTAValidation.Error SourceInternedRows.State Symbol)
      (checked : FTAValidation.mkFTA (encode value) (interpreted (rawRows rows keys value) (fun _ _ => true)) = .error error) :
      Execution given assumptions milliseconds check bound value state (.error (.invalidFTA error)) final
  | returned (state final : C) (rows : Rows Symbol Guard) (keys : List Nat)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
      (closed : value.free = []) (trace : Trace state (fun _ => none) [value] rows final)
      (checked : FTAValidation.mkFTA (encode value) (interpreted (rawRows rows keys value) (fun _ _ => true)) =
        .ok (interpreted (queryRows rows keys value) (fun _ _ => true)))
      (result : SourceSizedLiquidExecution.Outcome Item (SourceSizedDecidedTable.Table SourceInternedRows.State (Term Symbol)))
      (work : Nat)
      (run : SourceSizedFiniteKeysNativeLiquid.NativeRun (queryRows rows keys value) (encode value)
        (normalized_validated (rawRows rows keys value) (encode value) checked)
        (SourceSolverNamePublic.Call given assumptions milliseconds check) bound result work) :
      Execution given assumptions milliseconds check bound value state
        (.ok (result.map fun inner => inner.map fun output => SourceSizedBoundedApiLaws.fromClasses (output (encode value)))) final

/-- An open physical root returns its conversion error and the identical cache. -/
theorem Execution.open_result (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (bound : Int) (value : V) (state final : C) (result : Result)
    (actual : Execution given assumptions milliseconds check bound value state result final) (isOpen : value.free ≠ []) :
    result = .error .openNode ∧ final = state := by
  cases actual <;> simp_all

end MicroCFTA.SourceFreshOrdinaryLiquidEntry
