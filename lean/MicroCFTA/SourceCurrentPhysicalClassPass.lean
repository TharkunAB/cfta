import MicroCFTA.SourceCurrentClassRequiredReady
import MicroCFTA.SourceCurrentSelectedClassRecords
import MicroCFTA.SourceCurrentClassFoldComplete

/-!
# Physical current entry through required paths and the class pass

The actual live accessor supplies proper original records. The completed
scan retains their positional selection. Required execution derives every
selected path domain at its actual returned heap. These domains derive a
finite class pass under the actual reached word-range plan. Each class
captures the forest returned by the preceding tail execution.
-/
namespace MicroCFTA.SourceCurrentPhysicalClassPass
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan SourceEqualityClassOrder
open InternedGuardedLanguage (meaning)
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

/-- A live physical entry and successful Scan derive required execution and a finite range-checked class pass. -/
theorem live_scan_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (records : List Record)
    (live : SourceEqualityPhysicalClassEntry.entry constraint inherited = .ok (.classes records))
    {values : List (Value Symbol Guard)} {selected : Constraints}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values (records.map Record.paths) before memo none selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ kept scanMemos requiredMemos prepared heap,
      SourceCurrentSelectedClassRecords.Retained trace records kept ∧
      kept.Sublist records ∧ kept.map Record.paths = selected ∧
      SourceCurrentClassScanGlobalMemos.ScanReads trace memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values prepared after.machine.heap heap scanMemos requiredMemos ∧
      Valid heap requiredMemos ∧ CostHeap heap ∧ FieldHeap heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      IdleReady top conjoin (advanceHeap after heap) ∧
      Keeps before.machine.heap heap ∧ Values heap prepared ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values after.machine.heap) prepared heap ∧
      (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared) ∧
      (∀ holds ambient terms,
        All₂ (meaning holds ambient) prepared terms ↔ All₂ (meaning holds ambient) values terms ∧
          SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
      ∀ clear : Guard → Bool,
        SourceEqualityClassFoldGraph.Ranges top conjoin clear top kept prepared (advanceHeap after heap) →
        ∃ results final,
          SourceEqualityClassFoldGraph.Pass top conjoin clear top kept prepared (advanceHeap after heap) results final ∧
          SourceEqualityClassFoldWorkerProofs.StableRun
            (fun e p h c n => SourceEqualityClassFoldWorker.pass top conjoin clear top e p h c n
              kept prepared (advanceHeap after heap)) results final ∧
          IdleReady top conjoin final ∧ Keeps before.machine.heap final.machine.heap ∧
          Values final.machine.heap results ∧
          SourceCurrentEmptinessMemo.Correct formulas solver final.machine.heap saved ∧
          (∀ path, SourceEqualityProjectionPathDomain.ForestClosed path prepared →
            SourceEqualityProjectionPathDomain.ForestClosed path results) ∧
          (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) := by
  have proper := SourceEqualityPhysicalClassEntry.live_proper constraint cached inherited records live
  obtain ⟨kept, retained, sublist, selectedPaths, physical⟩ :=
    SourceCurrentSelectedClassRecords.live_retained_records constraint cached inherited records live trace
  obtain ⟨scanMemos, requiredMemos, prepared, heap, scanReads, requiredReads, requiredValid, _extends, _query,
      requiredReady, requiredCosts, requiredFields, fourth, fourthExtends, requiredKeeps, _scanKeeps,
      _semantic, _originalValues, resultValues, stable, _domain, pathDomains, language⟩ :=
    SourceCurrentClassRequiredReady.scan_required_ready trace ready available costs fields proper formulas solver correct memos valid
  refine ⟨kept, scanMemos, requiredMemos, prepared, heap, retained, sublist, selectedPaths,
    scanReads, requiredReads, requiredValid, requiredCosts, requiredFields, fourth, fourthExtends,
    requiredReady, requiredKeeps, resultValues, stable, pathDomains, (fun holds ambient terms => (language holds ambient terms).1), ?_⟩
  intro clear ranges
  have domains : ∀ record ∈ kept, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared := by
    intro record included path member
    apply pathDomains path
    rw [← selectedPaths]
    exact List.mem_flatten.mpr ⟨record.paths, List.mem_map.mpr ⟨record, included, rfl⟩, member⟩
  obtain ⟨results, final, pass, finalReady, finalKeeps, finalValues, preserved, executed⟩ :=
    SourceCurrentClassFoldComplete.pass_complete top conjoin clear top ranges
      (fun record member => (physical record member).1)
      (fun record member => (physical record member).2.2) requiredReady resultValues domains
  exact ⟨results, final, pass, executed, finalReady, requiredKeeps.trans finalKeeps, finalValues,
    SourceCurrentEmptinessMemo.grows formulas solver finalKeeps saved fourth,
    preserved, fun path member => preserved _ (pathDomains path member)⟩

end MicroCFTA.SourceCurrentPhysicalClassPass
