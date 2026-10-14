import MicroCFTA.SourceFreshOrdinaryNativeEntry

/-!
# Exact reference results for every actual public native entry

The physical prechecks determine all early returns. For the row branch,
the actual cold trace derives complete heap and table invariants. Actual
native compilation then gives the identical complete reference query record.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeEntry
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourceFreshOrdinaryNativeEntryPrecheck (check)

variable {bits : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (value : Value (Label Formula) (Constraint Formula))

local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) (Label Formula) (Constraint Formula)
local notation "Api" => SourceSizedDispatcher.Api (Label Formula)

/-- Every actual public native execution retains ready memos and the exact complete reference result. -/
theorem execution_correct (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value) (ranges : Ranges emptyGuard conjoin order value state)
    (result : Except SourceCyclicAutomaton.Error Api) (after : N)
    (actual : Execution emptyGuard conjoin formulas solver order value state result after) :
    SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧ Reference formulas solver order value state result := by
  cases actual with
  | empty selected => exact ⟨ready, .empty state selected⟩
  | openRoot selected => exact ⟨ready, .openRoot state selected⟩
  | rows after rows final domain supported closed active selected trace result native =>
      have valueClosed := ((SourceFreshOrdinaryNativeEntryPrecheck.check_rows_iff value).mp selected).2
      obtain ⟨finalReady, _, _, _, _, _, resident, replayed, children, _, _, _, invariant⟩ :=
        SourceFreshOrdinaryColdNativeTable.for_trace emptyGuard conjoin state ready value available valueClosed rows final trace
      have capacity := (show ∀ rows final domain supported closed active,
          Trace state.machine.heap (fun _ => none) [value] rows final →
            SourceFreshOrdinaryNativeCompiler.CapacityRanges emptyGuard conjoin final rows (keys final rows) value
              domain supported closed [] active order (advance state ⟨final, state.machine.domains⟩) from by
          simpa only [Ranges, selected, ↓reduceIte] using ranges) rows final domain supported closed active trace
      have wordRanges := SourceFreshOrdinaryNativeCompiler.ranges_of_capacity emptyGuard conjoin final rows (keys final rows) value
        domain supported closed [] active order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
        replayed resident children _ invariant capacity
      obtain ⟨retained, compiled⟩ := SourceFreshOrdinaryNativeCompiler.execution_correct emptyGuard conjoin final rows (keys final rows) value
        domain supported closed [] active formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
        replayed resident children _ invariant wordRanges result after native
      have mapped : result.map (fun output => SourceSizedDispatcher.optimizedApi output
            (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active).root) =
          result.map (fun output => SourceSizedDispatcher.referenceApi output
            (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active).root) := by
        cases result with
        | error error => rfl
        | ok output =>
            exact congrArg Except.ok (SourceFreshOrdinaryNativeCompiler.api_record emptyGuard conjoin final rows (keys final rows) value
              domain supported closed [] active formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
              replayed resident children _ invariant wordRanges output after native)
      refine ⟨retained.1, ?_⟩
      rw [mapped]
      exact .rows state rows final domain supported closed active selected trace result compiled

/-- Every ready public entry has finite actual execution; only its nonempty closed branch reads rows. -/
theorem complete (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value)
    (normalized : InternedFreshOrdinaryConstraintHeap.Heap
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) state.machine.heap)
    (ranges : Ranges emptyGuard conjoin order value state) :
    ∃ result after, Execution emptyGuard conjoin formulas solver order value state result after ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧ Reference formulas solver order value state result := by
  have finish (result : Except SourceCyclicAutomaton.Error Api) (after : N)
      (actual : Execution emptyGuard conjoin formulas solver order value state result after) :
      ∃ result after, Execution emptyGuard conjoin formulas solver order value state result after ∧
        SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧ Reference formulas solver order value state result :=
    ⟨result, after, actual, execution_correct emptyGuard conjoin formulas solver order value state ready available ranges result after actual⟩
  cases selected : check value with
  | empty => exact finish _ _ (.empty state selected)
  | openRoot => exact finish _ _ (.openRoot state selected)
  | rows =>
      have valueClosed := ((SourceFreshOrdinaryNativeEntryPrecheck.check_rows_iff value).mp selected).2
      obtain ⟨rows, final, _, _, trace, _, finalReady, _, _, _, _, supported,
          resident, replayed, children, _, domain, closed, invariant⟩ :=
        SourceFreshOrdinaryColdNativeTable.collect emptyGuard conjoin state ready value available valueClosed
      have inputs : SourceColdSharedRows.Inputs state.machine.heap [value] := by
        intro child member
        simpa only [List.mem_singleton.mp member] using And.intro available valueClosed
      have finalHeap := trace.constraint_heap (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities)
        ready.semantic ready.covered normalized inputs
      let active := SourceFreshOrdinaryColdSharedRows.table_constraints _ final finalHeap rows resident (keys final rows) domain value
      have capacity := (show ∀ rows final domain supported closed active,
          Trace state.machine.heap (fun _ => none) [value] rows final →
            SourceFreshOrdinaryNativeCompiler.CapacityRanges emptyGuard conjoin final rows (keys final rows) value
              domain supported closed [] active order (advance state ⟨final, state.machine.domains⟩) from by
          simpa only [Ranges, selected, ↓reduceIte] using ranges) rows final domain supported closed active trace
      obtain ⟨result, after, native, _, _⟩ := SourceFreshOrdinaryNativeCompiler.complete_capacity emptyGuard conjoin final rows (keys final rows) value
        domain supported closed [] active formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
        replayed resident children _ invariant capacity
      exact finish _ _ (.rows state after rows final domain supported closed active selected trace result native)

end MicroCFTA.SourceFreshOrdinaryNativeEntry
