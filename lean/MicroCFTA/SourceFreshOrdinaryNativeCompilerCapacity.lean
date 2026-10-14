import MicroCFTA.SourceFreshOrdinaryNativeCompilerApi
import MicroCFTA.SourceFreshOrdinaryNativeKeyCapacity

/-!
# Actual compiler completion from reached cache capacity

Empty, open, and constrained branches require no native callback capacity.
The ordered scan checks only actual continuing queries. Actual cache bounds
then derive the complete compiler's native word-safety contract.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCompiler
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Supported ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)

section Input
variable {bits : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (rows : Rows (Label Formula) (Constraint Formula)) (keys : List Nat)
    (value : Value (Label Formula) (Constraint Formula))
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (supported : Supported rows value)
    (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys value))
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows keys value) state →
      SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)

local notation "raw" => SourceColdSharedRows.table rows keys value
local notation "input" => SourceFreshOrdinaryColdCyclic.input rows keys value domain supported closed freeVariables active
local notation "base" => SourceCyclicRows.preparedInput input order (fun _ => 0)
local notation "K" => SourceDenseRows.Member (SourceDenseRows.keys raw)
local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) (Label Formula) (Constraint Formula)
local notation "A" => SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true)
local notation "queries" => SourceFreshOrdinaryNativeKeyScan.edgeQueries (List.attach (SourceDenseRows.keys raw)) A
local notation "edgeStep" => SourceFreshOrdinaryNativeKeyScan.EdgeExecution emptyGuard conjoin source Subtype.val
local notation "edgeRange" => SourceFreshOrdinaryNativeKeyScan.EdgeAllowed emptyGuard conjoin source Subtype.val
local notation "invariant" => SourceFreshOrdinaryNativeKeyScan.Invariant emptyGuard conjoin source

/-- Only actual reached native callbacks require capacity in the source's three supplies. -/
noncomputable def CapacityRanges (state : N) : Prop :=
  if (input).emptyRoot then True
  else if !(input).freeVariables.isEmpty then True
  else if SourceCyclicAutomaton.hasConstraints base then True
  else SourceShortCircuitScan.Ranges false edgeStep
    (SourceFreshOrdinaryNativeKeyCapacity.EdgeAllowed bits emptyGuard conjoin source Subtype.val) queries state

local notation "execution" => Execution emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
local notation "rangeCheck" => Ranges emptyGuard conjoin source rows keys value domain supported closed freeVariables active order

variable (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (replayed : ReplayedRows source rows) (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)

include semantic covered guarded budgetHeap replayed resident closedRows

local notation "capacityCheck" => CapacityRanges emptyGuard conjoin source rows keys value domain supported closed freeVariables active order

omit [DecidableEq Key] in
/-- Actual compiler capacity checks derive its native word contract after the real prechecks. -/
theorem ranges_of_capacity (state : N) (valid : invariant state) (capacity : capacityCheck state) : rangeCheck state := by
  cases emptyRoot : (input).emptyRoot with
  | true => simp [Ranges, emptyRoot]
  | false =>
      cases closedRoot : (input).freeVariables.isEmpty with
      | false => simp [Ranges, emptyRoot, closedRoot]
      | true =>
          cases checked : SourceCyclicAutomaton.hasConstraints base with
          | true => simp [Ranges, emptyRoot, closedRoot, checked]
          | false =>
              have reached := by simpa [CapacityRanges, emptyRoot, closedRoot, checked] using capacity
              have words := SourceFreshOrdinaryNativeKeyCapacity.scan_ranges bits emptyGuard conjoin source semantic covered guarded budgetHeap
                rows replayed resident closedRows keys domain value closed state valid reached
              simpa [Ranges, emptyRoot, closedRoot, checked] using words

/-- Reached cache capacity gives finite actual compiler execution and the literal reference result. -/
theorem complete_capacity (state : N) (valid : invariant state) (capacity : capacityCheck state) :
    ∃ result after, execution state result after ∧ invariant after ∧
      SourceCyclicRows.compile formulas solver input order = some result := by
  exact complete emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid
    (ranges_of_capacity emptyGuard conjoin source rows keys value domain supported closed freeVariables active order
      semantic covered guarded budgetHeap replayed resident closedRows state valid capacity)

end Input
end MicroCFTA.SourceFreshOrdinaryNativeCompiler
