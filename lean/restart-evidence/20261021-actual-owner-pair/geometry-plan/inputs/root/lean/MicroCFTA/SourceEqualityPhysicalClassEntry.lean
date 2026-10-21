import MicroCFTA.SourceCurrentClassEntryGlobalMemos
import MicroCFTA.SourceEqualityConstraintAllocation

/-!
# Derived physical records at the current class-scan entry

The computed equality accessor derives coherent ascending records from its
normalized stored field. A live precheck sorts those original records. The
current memo-entry theorem therefore needs no supplied record readback.
Initial machine and memo invariants remain explicit. This module does not
initialize the source equality interner or transfer lazy runtime execution.
-/
namespace MicroCFTA.SourceEqualityPhysicalClassEntry
open Language EqualityNormalize SourceEqualityClassOrder
open SourceEqualityGuardReadback (Cached)
open SourceEqualityDescend (WellFormed)

/-- The computed source accessor derives its physical payload and literal class readback. -/
theorem own_complete (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : Cached constraint.equalities) :
    ∃ payload, SourceEqualityPhysicalPayload.own constraint = .ok payload ∧ WellFormed payload ∧
      SourceEqualityInheritedPayload.classes payload = SourceCompactGuards.sourceEqualities constraint := by
  have normalized := SourceEqualityGuardReadback.source_cached constraint cached
  obtain ⟨payload, done, wellFormed, _⟩ := SourceEqualityInheritedPayload.read_complete (Symbol := Unit)
    (SourceCompactGuards.sourceEqualities constraint) normalized
  exact ⟨payload, done, wellFormed, SourceEqualityConstraintAllocation.read_classes _ normalized payload done⟩

/-- Every actual successful accessor receipt has the derived physical invariant and exact classes. -/
theorem own_verified (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : Cached constraint.equalities) (payload : SourceEqualityPrecheck.Constraint)
    (done : SourceEqualityPhysicalPayload.own constraint = .ok payload) :
    WellFormed payload ∧
      SourceEqualityInheritedPayload.classes payload = SourceCompactGuards.sourceEqualities constraint := by
  obtain ⟨actual, completed, wellFormed, readback⟩ := own_complete constraint cached
  have same : actual = payload := Except.ok.inj (completed.symm.trans done)
  subst actual
  exact ⟨wellFormed, readback⟩

/-- Compute the own accessor before the source empty, contradiction, and original-order guards. -/
noncomputable def entry (constraint : SourceSymbolicIndex.Constraint Formula)
    (inherited : SourceEqualityPrecheck.Constraint) : Except String SourceEqualityPrecheck.Branch := do
  let own ← SourceEqualityPhysicalPayload.own constraint
  SourceEqualityPrecheck.precheck own inherited

/-- A successful actual accessor receipt fixes the following precheck without another constructor. -/
theorem entry_of_own (constraint : SourceSymbolicIndex.Constraint Formula)
    (inherited payload : SourceEqualityPrecheck.Constraint)
    (done : SourceEqualityPhysicalPayload.own constraint = .ok payload) :
    entry constraint inherited = SourceEqualityPrecheck.precheck payload inherited := by
  unfold entry
  rw [done]
  rfl

/-- Normalized stored fields derive a complete checked entry without a supplied answer. -/
theorem entry_complete (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : Cached constraint.equalities) (inherited : SourceEqualityPrecheck.Constraint) :
    ∃ branch, entry constraint inherited = .ok branch := by
  obtain ⟨own, computed, _, _⟩ := own_complete constraint cached
  obtain ⟨branch, done⟩ := SourceEqualityPrecheck.precheck_safe own inherited
  exact ⟨branch, (entry_of_own constraint inherited own computed).trans done⟩

/-- A live actual entry derives the original records and each sorted physical field invariant. -/
theorem live_records (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : Cached constraint.equalities) (inherited : SourceEqualityPrecheck.Constraint)
    (output : List Record) (live : entry constraint inherited = .ok (.classes output)) :
    ∃ records, SourceEqualityPhysicalPayload.own constraint = .ok (some records) ∧
      SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths) ∧
      SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output) ∧
      output = ordered records ∧
      ∀ record ∈ output, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  obtain ⟨own, computed, wellFormed, readback⟩ := own_complete constraint cached
  have checked : SourceEqualityPrecheck.precheck own inherited = .ok (.classes output) :=
    (entry_of_own constraint inherited own computed).symm.trans live
  obtain ⟨records, same, order, _⟩ := SourceEqualityPrecheck.live_payload own inherited output checked
  rw [same] at computed wellFormed readback checked
  refine ⟨records, computed, readback.symm, checked, order, ?_⟩
  rw [order]
  intro record member
  exact wellFormed records rfl record ((ordered_perm records).mem_iff.mp member)

/-- The actual live output contains only nontrivial original classes. -/
theorem live_active (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : Cached constraint.equalities) (inherited : SourceEqualityPrecheck.Constraint)
    (output : List Record) (live : entry constraint inherited = .ok (.classes output)) :
    Active (output.map Record.paths) := by
  obtain ⟨_, _, _, _, _, valid⟩ := live_records constraint cached inherited output live
  intro paths member
  obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
  exact (valid record included).2.2

open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
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

/-- The computed live entry derives proper paths without an original-record premise. -/
theorem live_proper (constraint : Guard) (cached : Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : entry constraint inherited = .ok (.classes output)) :
    ∀ paths ∈ output.map Record.paths, ∀ path ∈ paths, path ≠ [] := by
  obtain ⟨records, _, readback, checked, _, _⟩ := live_records constraint cached inherited output live
  exact SourceCurrentClassEntryGlobalMemos.live_proper constraint cached records readback inherited output checked

/-- The actual reached scan derives its memo and heap invariants from the computed physical entry. -/
theorem live_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : entry constraint inherited = .ok (.classes output))
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
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨records, _, readback, checked, _, _⟩ := live_records constraint cached inherited output live
  exact SourceCurrentClassEntryGlobalMemos.live_memos constraint cached records readback inherited output checked
    trace ready available costs fields formulas solver correct memos valid

end MicroCFTA.SourceEqualityPhysicalClassEntry
