import MicroCFTA.SourceCurrentPhysicalClassPass
import MicroCFTA.SourceCurrentClassFoldLanguage
import MicroCFTA.SourceCurrentClassEditHeapEffects
import MicroCFTA.SourceCurrentClassFoldQueryMemos

/-!
# Physical current class passes with independent language and heap effects

The computed live entry fixes the original physical records. The actual
successful scan derives positional selection and required execution.
Actual class range checks derive a finite pass on that returned forest.
The pass retains open unselected siblings, costs, and normalized fields.
Class satisfaction supplies every original required path in the term.
-/
namespace MicroCFTA.SourceCurrentPhysicalClassPassLanguage
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

/-- Satisfied nontrivial original records supply the exact conditional forest requirements. -/
theorem satisfied_required (records : List Record) (symbol : S) (terms : List (Term S))
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (satisfied : ∀ record ∈ records, ClassSat (.node symbol terms) record.paths) :
    SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths (records.map Record.paths)) terms := by
  have existsPath : ∀ path ∈ (records.map Record.paths).flatten, ∃ part, (Term.node symbol terms).atPath path = some part := by
    intro path member
    obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
    obtain ⟨record, member, same⟩ := List.mem_map.mp included
    subst paths
    exact class_member_exists (.node symbol terms) record.paths (active record member) (satisfied record member) path present
  have matched := (SourceEqualityNeededMeaning.build_exact
    (SourceEqualitySelectedRequired.paths (records.map Record.paths)) (.node symbol terms)).mpr
      ((SourceEqualitySelectedRequired.paths_exist _ _).mpr existsPath)
  have valid := SourceEqualityNeeded.build_valid (SourceEqualitySelectedRequired.paths (records.map Record.paths))
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (records.map Record.paths)) with
  | node entries =>
      rw [SourceEqualityRequiredAPI.ForestRequired, compiled]
      have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from
        by simpa only [SourceEqualityNeeded.Valid, compiled] using valid).1
      apply (SourceEqualityRequiredForestMeaning.required_zero entries ordered terms).mpr
      rw [compiled, SourceEqualityNeededMeaning.Matches] at matched
      intro index needed member term selected
      obtain ⟨actual, found, actualMatched⟩ := matched index needed member
      have same : actual = term := Option.some.inj (found.symm.trans selected)
      subst actual
      exact actualMatched

/-- The live physical caller derives finite actual class execution, physical fields, and independent language bounds. -/
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
      Valid heap requiredMemos ∧ CostHeap heap ∧ FieldHeap heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧ SourceCurrentEmptinessMemo.Extends memo saved ∧
      IdleReady top conjoin (advanceHeap after heap) ∧ Keeps before.machine.heap heap ∧ Values heap prepared ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values after.machine.heap) prepared heap ∧
      (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared) ∧
      (∀ terms, All₂ (meaning holds ambient) prepared terms ↔ All₂ (meaning holds ambient) values terms ∧
        SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
      ∀ _ranges : SourceEqualityClassFoldGraph.Ranges top conjoin SourceMemoGate.plain top kept prepared (advanceHeap after heap),
        ∃ results final, ∃ pass :
          SourceEqualityClassFoldGraph.Pass top conjoin SourceMemoGate.plain top kept prepared (advanceHeap after heap) results final,
          SourceEqualityClassFoldWorkerProofs.StableRun
            (fun e p h c n => SourceEqualityClassFoldWorker.pass top conjoin SourceMemoGate.plain top e p h c n
              kept prepared (advanceHeap after heap)) results final ∧
          IdleReady top conjoin final ∧ CostHeap final.machine.heap ∧ FieldHeap final.machine.heap ∧
          Keeps before.machine.heap final.machine.heap ∧ Keeps heap final.machine.heap ∧
          Values final.machine.heap values ∧ Values final.machine.heap prepared ∧ Values final.machine.heap results ∧
          SourceCurrentEmptinessMemo.Correct formulas solver final.machine.heap saved ∧
          (∀ path, SourceEqualityProjectionPathDomain.ForestClosed path prepared →
            SourceEqualityProjectionPathDomain.ForestClosed path results) ∧
          (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) ∧
          (∀ symbol terms,
            (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms ∧
              SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
            ((∀ record ∈ kept, ClassSat (.node symbol terms) record.paths) →
              (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms))) ∧
          ∃ finalMemos,
            SourceCurrentClassFoldQueryMemos.PassReads pass requiredMemos finalMemos ∧
            SourceCurrentSubsumesQueryMemos.Effect heap final.machine.heap requiredMemos finalMemos := by
  obtain ⟨_, _, _, _, _, physical⟩ := SourceEqualityPhysicalClassEntry.live_records constraint cached inherited records live
  obtain ⟨kept, scanMemos, requiredMemos, prepared, heap, retained, sublist, selectedPaths, scanReads, requiredReads,
      requiredValid, requiredCosts, requiredFields, fourth, fourthExtends, requiredReady, requiredKept, preparedValues,
      requiredStable, pathDomains, requiredLanguage, complete⟩ :=
    SourceCurrentPhysicalClassPass.live_scan_pass constraint cached inherited records live trace ready available costs fields formulas solver correct memos valid
  refine ⟨kept, scanMemos, requiredMemos, prepared, heap, retained, sublist, selectedPaths, scanReads, requiredReads,
    requiredValid, requiredCosts, requiredFields, fourth, fourthExtends, requiredReady, requiredKept, preparedValues,
    requiredStable, pathDomains, requiredLanguage holds ambient, ?_⟩
  intro ranges
  have coherent : ∀ record ∈ kept, Coherent record := fun record member => (physical record (sublist.subset member)).1
  have active : ∀ record ∈ kept, Nontrivial record.paths := fun record member => (physical record (sublist.subset member)).2.2
  have domains : ∀ record ∈ kept, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) prepared := by
    intro record included path member
    apply pathDomains path
    rw [← selectedPaths]
    exact List.mem_flatten.mpr ⟨record.paths, List.mem_map.mpr ⟨record, included, rfl⟩, member⟩
  obtain ⟨results, final, pass, executed, finalReady, finalKept, resultValues, finalFourth, preserved, finalPaths⟩ :=
    complete SourceMemoGate.plain ranges
  have stage := SourceCurrentClassFoldDomains.pass_domains top conjoin SourceMemoGate.plain top pass coherent active requiredReady preparedValues domains
  have heapEffects := SourceCurrentClassEditHeapEffects.pass_fields pass coherent active requiredReady preparedValues domains requiredCosts requiredFields
  obtain ⟨finalMemos, finalReads, memoEffects⟩ :=
    SourceCurrentClassFoldQueryMemos.pass_memos pass coherent active requiredReady requiredCosts preparedValues domains requiredMemos requiredValid
  refine ⟨results, final, pass, executed, finalReady, heapEffects.1, heapEffects.2, finalKept, stage.2.1,
    (fun value member => finalKept.available value (available value member)),
    (fun value member => stage.2.1.available value (preparedValues value member)), resultValues,
    finalFourth, preserved, finalPaths, ?_, finalMemos, finalReads, memoEffects⟩
  intro symbol terms
  have bounds := SourceCurrentClassFoldLanguage.pass_language top conjoin SourceMemoGate.plain top holds ambient clearTrue topTrue conjoined
    pass coherent active requiredReady preparedValues domains symbol terms
  refine ⟨fun accepted => (requiredLanguage holds ambient terms).mp (bounds.1 accepted), ?_⟩
  intro satisfied
  have required := satisfied_required kept symbol terms active satisfied
  rw [selectedPaths] at required
  exact ⟨fun accepted => ((requiredLanguage holds ambient terms).mp (bounds.1 accepted)).1,
    fun accepted => bounds.2 satisfied ((requiredLanguage holds ambient terms).mpr ⟨accepted, required⟩)⟩

end MicroCFTA.SourceCurrentPhysicalClassPassLanguage
