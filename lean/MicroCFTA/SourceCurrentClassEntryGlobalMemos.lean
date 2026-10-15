import MicroCFTA.SourceCurrentClassScanGlobalMemos
import MicroCFTA.SourceEqualityPrecheck
import MicroCFTA.SourceEqualityGuardReadback
import MicroCFTA.EqualityLeafProjectionProperPaths

/-!
# Current memoized scans at the exact normalized accessor entry

Cached accessor classes are active and contradiction-free. Every original
path is therefore proper. The actual precheck sorts the original records
and preserves that fact. The reached scan then derives its final memo and
heap invariants without a separate proper-path premise.

Exact accessor readback and initial caller invariants remain explicit.
These results do not extract native physical records or initialize a caller.
-/
namespace MicroCFTA.SourceCurrentClassEntryGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassOrder SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan SourceCurrentClassScanGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- The exact cached accessor and live precheck derive proper paths in the ordered original records. -/
theorem live_proper (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths))
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output)) :
    ∀ paths ∈ output.map Record.paths, ∀ path ∈ paths, path ≠ [] := by
  have normal := SourceEqualityGuardReadback.source_cached constraint cached (records.map Record.paths) readback
  have proper := EqualityLeafProjectionProperPaths.active_proper _ normal.1 normal.2.1
  obtain ⟨original, own, same, _⟩ := SourceEqualityPrecheck.live_payload (some records) inherited output live
  have identical : records = original := Option.some.inj own
  subst original
  rw [same]
  intro paths member path present
  exact proper paths (((ordered_perm records).map Record.paths).mem_iff.mp member) path present

/-- The actual ordered source entry derives all reached scan invariants from the initial caller state. -/
theorem live_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths))
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output))
    {values : List (Value Symbol Guard)} {selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values (output.map Record.paths) before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, ScanReads trace memos final ∧ Valid after.machine.heap final ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved :=
  scan_memos trace ready available costs fields (live_proper constraint cached records readback inherited output live)
    formulas solver correct memos valid

end MicroCFTA.SourceCurrentClassEntryGlobalMemos
