import MicroCFTA.SourceFreshOrdinaryNativeKeyScan
import MicroCFTA.SourceFreshOrdinaryNativeCallbackCapacity
import MicroCFTA.SourceShortCircuitScanRanges

/-!
# Actual ambiguity scans from reached cache capacities

Each reached child query checks only its actual native cache counters.
Resident finite input keys derive operand provenance. Actual continuing
callbacks retain the source cache invariant for the next query.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeKeyCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourceFreshOrdinaryColdKeys (physical)
open SourceFreshOrdinaryNativeKeyScan (Step EdgeExecution Invariant edgeQueries)

/-- Only actual prefixes of the reached child callback require cache capacity. -/
def Allowed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) (pair : Key × Key)
    (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard) : Prop :=
  SourceRecursiveIntersectionNativeCapacity.CacheRanges bits emptyGuard conjoin
    (.node ⟨IntersectionEmptyDomain.emptyDomain, physical source (encode pair.1), physical source (encode pair.2)⟩ .pure) state

/-- Mismatched symbols or arities require no child capacity checks. -/
def EdgeAllowed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) (pair : Edge Key Symbol × Edge Key Symbol)
    (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard) : Prop :=
  if pair.1.label = pair.2.label ∧ pair.1.children.length = pair.2.children.length then
    SourceShortCircuitScan.Ranges true (Step emptyGuard conjoin source encode) (Allowed bits emptyGuard conjoin source encode)
      (pair.1.children.zip pair.2.children) state
  else True

section Input
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows source rows)
    (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys root))

local notation "raw" => SourceColdSharedRows.table rows keys root
local notation "K" => SourceDenseRows.Member (SourceDenseRows.keys raw)
local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard
local notation "A" => SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true)
local notation "invariant" => Invariant emptyGuard conjoin source
local notation "step" => Step emptyGuard conjoin source Subtype.val
local notation "allowed" => Allowed bits emptyGuard conjoin source Subtype.val
local notation "oldAllowed" => SourceFreshOrdinaryNativeKeyScan.Allowed emptyGuard conjoin source Subtype.val

include semantic resident domain

/-- Canonical finite input records derive every reached child request's word safety from actual cache counters. -/
theorem allowed_words (pair : K × K) (state : N) (valid : invariant state) (capacity : allowed pair state) :
    oldAllowed pair state := by
  have leftDeclared := SourceFreshOrdinaryColdKeys.table_declared rows keys domain root pair.1.val pair.1.property
  have rightDeclared := SourceFreshOrdinaryColdKeys.table_declared rows keys domain root pair.2.val pair.2.property
  have left := (SourceFreshOrdinaryColdKeys.physical_record source semantic rows resident pair.1.val leftDeclared).1
  have right := (SourceFreshOrdinaryColdKeys.physical_record source semantic rows resident pair.2.val rightDeclared).1
  exact SourceRecursiveIntersectionNativeCapacity.node_wordRanges bits emptyGuard conjoin _ state valid.1.valid
    ⟨empty_domain state.machine, left.grows source state.machine.heap valid.2.1 valid.2.2,
      right.grows source state.machine.heap valid.2.1 valid.2.2⟩ capacity

include covered guarded budgetHeap replayed closedRows closed

/-- Actual reached child capacity checks derive the complete ordered child word contract. -/
theorem children_ranges (queries : List (K × K)) (state : N) (valid : invariant state)
    (ranges : SourceShortCircuitScan.Ranges true step allowed queries state) :
    SourceShortCircuitScan.Ranges true step oldAllowed queries state := by
  have convert := allowed_words bits emptyGuard conjoin source semantic rows resident keys domain root
  apply SourceShortCircuitScan.Ranges.transfer true step allowed oldAllowed invariant convert _ queries state valid ranges
  intro pair current after ready capacity actual
  exact (SourceFreshOrdinaryNativeKeyScan.callback_correct emptyGuard conjoin source semantic covered guarded budgetHeap
    rows replayed resident closedRows keys domain root closed pair current ready (convert pair current ready capacity) true after actual).1

/-- Matching edge capacity checks derive word safety only for their actual reached child scan. -/
theorem edge_ranges (pair : Edge K Symbol × Edge K Symbol) (state : N) (valid : invariant state)
    (ranges : EdgeAllowed bits emptyGuard conjoin source Subtype.val pair state) :
    SourceFreshOrdinaryNativeKeyScan.EdgeAllowed emptyGuard conjoin source Subtype.val pair state := by
  by_cases same : pair.1.label = pair.2.label ∧ pair.1.children.length = pair.2.children.length
  · have reached := by simpa [EdgeAllowed, same] using ranges
    simpa [SourceFreshOrdinaryNativeKeyScan.EdgeAllowed, same] using
      children_ranges bits emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed
        (pair.1.children.zip pair.2.children) state valid reached
  · simp [SourceFreshOrdinaryNativeKeyScan.EdgeAllowed, same]

/-- Reached all-row capacity checks derive the original full native scan word contract. -/
theorem scan_ranges (state : N) (valid : invariant state)
    (ranges : SourceShortCircuitScan.Ranges false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (EdgeAllowed bits emptyGuard conjoin source Subtype.val) (edgeQueries (List.attach (SourceDenseRows.keys raw)) A) state) :
    SourceShortCircuitScan.Ranges false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (SourceFreshOrdinaryNativeKeyScan.EdgeAllowed emptyGuard conjoin source Subtype.val)
      (edgeQueries (List.attach (SourceDenseRows.keys raw)) A) state := by
  have convert := edge_ranges bits emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed
  apply SourceShortCircuitScan.Ranges.transfer false _ _ _ invariant convert _ _ state valid ranges
  intro pair current after ready capacity actual
  exact (SourceFreshOrdinaryNativeKeyScan.edge_correct emptyGuard conjoin source semantic covered guarded budgetHeap
    rows replayed resident closedRows keys domain root closed pair current ready (convert pair current ready capacity) false after actual).1

end Input
end MicroCFTA.SourceFreshOrdinaryNativeKeyCapacity
