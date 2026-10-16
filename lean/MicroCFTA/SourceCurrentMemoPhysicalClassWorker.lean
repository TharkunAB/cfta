import MicroCFTA.SourceCurrentPhysicalClassPassLanguage
import MicroCFTA.SourceCurrentMemoClassWorkerComplete
import MicroCFTA.SourceCurrentMemoClassFieldHeap

/-!
# Physical Scan and required paths through the executable memo-aware class pass

The live entry supplies the original physical records. The actual successful
Scan selects those records and derives finite required-path execution.
The returned heap starts the memo-aware class pass. Its global tables can
contain valid entries. Only the completed merge table starts empty.
The same returned pass supplies stable execution and the language, field,
and memo conclusions. The bounds do not measure runtime complexity.
Successful Scan and the reached range plan remain explicit premises.
-/
namespace MicroCFTA.SourceCurrentMemoPhysicalClassWorker
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

/-- The physical entry derives one finite memo-aware pass with its actual fields, language, and global reads. -/
theorem live_scan_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, SourceMemoGate.plain guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
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
      Valid heap requiredMemos ∧ Extends scanMemos.unfolding requiredMemos.unfolding ∧
      requiredMemos.query = scanMemos.query ∧ CostHeap heap ∧ FieldHeap heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧ SourceCurrentEmptinessMemo.Extends memo saved ∧
      IdleReady top conjoin (advanceHeap after heap) ∧ Keeps before.machine.heap heap ∧ Values heap prepared ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values after.machine.heap) prepared heap ∧
      (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared) ∧
      (∀ terms, All₂ (meaning holds ambient) prepared terms ↔ All₂ (meaning holds ambient) values terms ∧
        SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
      ∀ _ranges : SourceCurrentMemoClassPass.Ranges top conjoin SourceMemoGate.plain top kept prepared
          (advanceHeap after heap) SourceCurrentMemoMergeGraph.empty,
        ∃ results final completed finalMemos, ∃ pass :
          SourceCurrentMemoClassPass.Pass top conjoin SourceMemoGate.plain top kept prepared
            (advanceHeap after heap) SourceCurrentMemoMergeGraph.empty results final completed,
          SourceCurrentMemoClassWorkerProofs.StableRun
            (fun e p h w c n => SourceCurrentMemoClassWorker.pass top conjoin SourceMemoGate.plain top
              e p h w c n kept prepared (advanceHeap after heap) SourceCurrentMemoMergeGraph.empty)
            results final completed ∧
          (∃ bound, ∀ fuel, bound ≤ fuel → SourceCurrentMemoClassWorker.pass top conjoin SourceMemoGate.plain top
            fuel fuel fuel fuel fuel fuel kept prepared (advanceHeap after heap) SourceCurrentMemoMergeGraph.empty =
              .done results final completed) ∧
          SourceCurrentMemoClassPassMemos.PassReads pass requiredMemos finalMemos ∧
          SourceCurrentSubsumesQueryMemos.Effect heap final.machine.heap requiredMemos finalMemos ∧
          IdleReady top conjoin final ∧ CostHeap final.machine.heap ∧ FieldHeap final.machine.heap ∧
          SourceCurrentMemoMergeEffects.Stored final.machine.heap completed ∧
          SourceCurrentMemoMergeLanguage.CacheCovers holds ambient completed ∧
          SourceCurrentMemoMergeOrigins.Produced SourceMemoGate.plain top completed ∧
          Keeps before.machine.heap final.machine.heap ∧ Keeps heap final.machine.heap ∧
          Values final.machine.heap values ∧ Values final.machine.heap prepared ∧ Values final.machine.heap results ∧
          SourceCurrentEmptinessMemo.Correct formulas solver final.machine.heap saved ∧
          (∀ path, SourceEqualityProjectionPathDomain.ForestClosed path prepared →
            SourceEqualityProjectionPathDomain.ForestClosed path results) ∧
          (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) ∧
          ∀ symbol terms,
            (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms ∧
              SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
            ((∀ record ∈ kept, ClassSat (.node symbol terms) record.paths) →
              (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms)) := by
  have proper := SourceEqualityPhysicalClassEntry.live_proper constraint cached inherited records live
  obtain ⟨kept, retained, sublist, selectedPaths, physical⟩ :=
    SourceCurrentSelectedClassRecords.live_retained_records constraint cached inherited records live trace
  obtain ⟨scanMemos, requiredMemos, prepared, heap, scanReads, requiredReads, requiredValid, requiredExtends, querySame,
      requiredReady, requiredCosts, requiredFields, fourth, fourthExtends, requiredKeeps, _scanKeeps,
      _semantic, originalValues, preparedValues, stable, _domain, pathDomains, language⟩ :=
    SourceCurrentClassRequiredReady.scan_required_ready trace ready available costs fields proper formulas solver correct memos valid
  refine ⟨kept, scanMemos, requiredMemos, prepared, heap, retained, sublist, selectedPaths, scanReads, requiredReads,
    requiredValid, requiredExtends, querySame, requiredCosts, requiredFields, fourth, fourthExtends, requiredReady,
    requiredKeeps, preparedValues, stable, pathDomains, (fun terms => (language holds ambient terms).1), ?_⟩
  intro ranges
  have coherent : ∀ record ∈ kept, Coherent record := fun record member => (physical record member).1
  have active : ∀ record ∈ kept, Nontrivial record.paths := fun record member => (physical record member).2.2
  have domains : ∀ record ∈ kept, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared := by
    intro record included path member
    apply pathDomains path
    rw [← selectedPaths]
    exact List.mem_flatten.mpr ⟨record.paths, List.mem_map.mpr ⟨record, included, rfl⟩, member⟩
  obtain ⟨results, final, completed, finalMemos, pass, executed, reads, effect, finalReady, finalCosts, stored,
      finalKeeps, resultValues, preserved, covered, origins, bounds⟩ :=
    SourceCurrentMemoClassWorkerComplete.source_cold top conjoin holds ambient clearTrue topTrue conjoined
      kept prepared (advanceHeap after heap) ranges coherent active requiredReady requiredCosts preparedValues domains requiredMemos requiredValid
  have uniform := SourceCurrentMemoClassWorkerProofs.uniform executed
  have finalFields := SourceCurrentMemoClassFieldHeap.pass_fields pass coherent active requiredReady requiredCosts
    (SourceCurrentMemoMergeEffects.stored_empty heap) preparedValues domains requiredFields
  refine ⟨results, final, completed, finalMemos, pass, executed, uniform, reads, effect, finalReady, finalCosts, finalFields, stored,
    covered, origins, requiredKeeps.trans finalKeeps, finalKeeps,
    (fun value member => finalKeeps.available value (originalValues value member)),
    (fun value member => finalKeeps.available value (preparedValues value member)), resultValues,
    SourceCurrentEmptinessMemo.grows formulas solver finalKeeps saved fourth,
    preserved, (fun path member => preserved _ (pathDomains path member)), ?_⟩
  intro symbol terms
  refine ⟨fun accepted => (language holds ambient terms).1.mp ((bounds symbol terms).1 accepted), ?_⟩
  intro satisfied
  have required := SourceCurrentPhysicalClassPassLanguage.satisfied_required kept symbol terms active satisfied
  rw [selectedPaths] at required
  exact ⟨fun accepted => ((language holds ambient terms).1.mp ((bounds symbol terms).1 accepted)).1,
    fun accepted => ((bounds symbol terms).2 satisfied).mpr ((language holds ambient terms).1.mpr ⟨accepted, required⟩)⟩

end MicroCFTA.SourceCurrentMemoPhysicalClassWorker
