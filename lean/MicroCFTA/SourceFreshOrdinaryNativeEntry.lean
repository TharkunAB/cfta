import MicroCFTA.SourceFreshOrdinaryCapacityNativeSized
import MicroCFTA.SourceFreshOrdinaryNativeEntryPrecheck
import MicroCFTA.SourceFreshOrdinaryColdNativeTrace
import MicroCFTA.SourceFreshOrdinaryNativeEmptyApi

/-!
# Public native compiler control before actual row preparation

Empty and open roots return without cold traversal or native callbacks.
Only a nonempty closed root reads its actual finite table. Its finite key
carrier stays inside that phase. All branches return one public query type.
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

local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) (Label Formula) (Constraint Formula)
local notation "C" => InternedConstructorTemplates.State (Label Formula) (Constraint Formula)
local notation "V" => Value (Label Formula) (Constraint Formula)
local notation "Api" => SourceSizedDispatcher.Api (Label Formula)

/-- Actual public execution checks the physical root before any cold or native work. -/
inductive Execution (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key) (value : V) :
    N → Except SourceCyclicAutomaton.Error Api → N → Prop where
  | empty (state : N) (selected : check value = .empty) :
      Execution emptyGuard conjoin formulas solver order value state (.ok SourceFreshOrdinaryNativeEmptyApi.api) state
  | openRoot (state : N) (selected : check value = .openRoot) :
      Execution emptyGuard conjoin formulas solver order value state (.error .openAutomaton) state
  | rows (state after : N) (rows : Rows (Label Formula) (Constraint Formula)) (final : C)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
      (supported : Supported rows value)
      (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value))
      (active : ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) value) key →
        SourceCompactGuards.ActiveOption edge.constraint.equalities)
      (selected : check value = .rows)
      (trace : Trace state.machine.heap (fun _ => none) [value] rows final)
      (result : Except SourceCyclicAutomaton.Error
        (Automaton (SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table rows (keys final rows) value))) (Label Formula)))
      (native : SourceFreshOrdinaryNativeCompiler.Execution emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
        formulas solver order (advance state ⟨final, state.machine.domains⟩) result after) :
      Execution emptyGuard conjoin formulas solver order value state
        (result.map fun output => SourceSizedDispatcher.optimizedApi output
          (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active).root) after

/-- Reference public results retain the same physical root checks and actual cold table. -/
inductive Reference (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key) (value : V) :
    N → Except SourceCyclicAutomaton.Error Api → Prop where
  | empty (state : N) (selected : check value = .empty) :
      Reference formulas solver order value state (.ok SourceFreshOrdinaryNativeEmptyApi.api)
  | openRoot (state : N) (selected : check value = .openRoot) :
      Reference formulas solver order value state (.error .openAutomaton)
  | rows (state : N) (rows : Rows (Label Formula) (Constraint Formula)) (final : C)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
      (supported : Supported rows value)
      (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value))
      (active : ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) value) key →
        SourceCompactGuards.ActiveOption edge.constraint.equalities)
      (selected : check value = .rows)
      (trace : Trace state.machine.heap (fun _ => none) [value] rows final)
      (result : Except SourceCyclicAutomaton.Error
        (Automaton (SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table rows (keys final rows) value))) (Label Formula)))
      (compiled : SourceCyclicRows.compile formulas solver
        (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active) order = some result) :
      Reference formulas solver order value state
        (result.map fun output => SourceSizedDispatcher.referenceApi output
          (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active).root)

/-- Capacity is checked only after an actual nonempty closed-root traversal. -/
noncomputable def Ranges (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (order : Label Formula → Key) (value : V) (state : N) : Prop :=
  if check value = .rows then
    ∀ (rows : Rows (Label Formula) (Constraint Formula)) (final : C)
      (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
      (supported : Supported rows value)
      (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value))
      (active : ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) value) key →
        SourceCompactGuards.ActiveOption edge.constraint.equalities),
      Trace state.machine.heap (fun _ => none) [value] rows final →
        SourceFreshOrdinaryNativeCompiler.CapacityRanges emptyGuard conjoin final rows (keys final rows) value
          domain supported closed [] active order (advance state ⟨final, state.machine.domains⟩)
  else True

variable (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (value : Value (Label Formula) (Constraint Formula))

/-- The empty root returns its direct query record and the identical native cache. -/
theorem Execution.empty_result (state after : N) (result : Except SourceCyclicAutomaton.Error Api)
    (actual : Execution emptyGuard conjoin formulas solver order value state result after) (selected : check value = .empty) :
    result = .ok SourceFreshOrdinaryNativeEmptyApi.api ∧ after = state := by
  cases actual <;> simp_all

/-- An open root returns its source error and the identical cache without row or native work. -/
theorem Execution.open_result (state after : N) (result : Except SourceCyclicAutomaton.Error Api)
    (actual : Execution emptyGuard conjoin formulas solver order value state result after) (selected : check value = .openRoot) :
    result = .error .openAutomaton ∧ after = state := by
  cases actual <;> simp_all

end MicroCFTA.SourceFreshOrdinaryNativeEntry
