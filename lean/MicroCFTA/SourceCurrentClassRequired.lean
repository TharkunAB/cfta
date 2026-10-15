import MicroCFTA.SourceCurrentClassScanSupport
import MicroCFTA.SourceCurrentRequiredLanguage
import MicroCFTA.SourceCurrentRequiredTipSupport

/-!
# Current successful class scans followed by exact required-path execution

The actual scan supplies its returned constructor heap and the selected
original paths. Their canonical union derives the required-worker domain.
The worker then has finite execution and exact filter language at that heap.
The scan memo invariants end at the scan heap. Their transfer through the
required worker and the later class edits remains a separate obligation.
-/
namespace MicroCFTA.SourceCurrentClassRequired
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan
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

/-- Original path witnesses cover the canonical union selected by the actual scan. -/
theorem selected_paths_exist [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo outcome selected after saved)
    (term : Term Symbol) (pathsExist : ∀ path ∈ classes.flatten, ∃ part, term.atPath path = some part) :
    ∀ path ∈ SourceEqualitySelectedRequired.paths selected,
      ∃ part, SymbolicSignedPaths.lookup term path = some part := by
  apply (SourceEqualitySelectedRequired.paths_exist selected term).mpr
  intro path member
  obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
  exact pathsExist path (List.mem_flatten.mpr ⟨paths, (selected_sublist trace).subset included, present⟩)

/-- A successful actual scan derives finite exact required filtering on its original child forest. -/
theorem scan_required_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo none selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final results requiredHeap,
      SourceCurrentClassScanGlobalMemos.ScanReads trace memos final ∧ Valid after.machine.heap final ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      SourceCurrentRequiredTipSupport.ForestTips source after.machine.heap
        (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) values ∧
      Keeps before.machine.heap requiredHeap ∧ Keeps after.machine.heap requiredHeap ∧
      SemanticReady requiredHeap ∧ Values requiredHeap values ∧ Values requiredHeap results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values after.machine.heap) results requiredHeap ∧
      ∀ holds ambient terms,
        (All₂ (meaning holds ambient) results terms ↔
          All₂ (meaning holds ambient) values terms ∧
            SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
        (∀ symbol, (∀ path ∈ classes.flatten, ∃ part, (Term.node symbol terms).atPath path = some part) →
          All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  obtain ⟨final, reads, finalValid, finalReady, finalCosts, finalFields, kept,
      finalValues, finalCorrect, extension, _gateReady, _origins, primary, support⟩ :=
    SourceCurrentClassScanSupport.scan_support trace ready available costs fields proper
      formulas solver correct memos valid
  have tips := SourceCurrentRequiredTipSupport.selected_domain finalReady.semantic finalValues primary
  obtain ⟨results, requiredHeap, requiredKept, requiredSemantic, requiredValues, stable⟩ :=
    SourceCurrentRequiredComplete.requireAll_complete source after.machine.heap finalReady.semantic
      (SourceEqualitySelectedRequired.paths selected) (SourceEqualitySelectedRequired.paths_nonnegative selected)
      values after.machine.heap finalReady.semantic finalValues (grows_refl _) support
  refine ⟨final, results, requiredHeap, reads, finalValid, finalReady, finalCosts, finalFields,
    finalCorrect, extension, tips, kept.trans requiredKept, requiredKept, requiredSemantic,
    (fun value member => requiredKept.available value (finalValues value member)), requiredValues, stable, ?_⟩
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  intro holds ambient terms
  refine ⟨SourceCurrentRequiredLanguage.requireAll_done source after.machine.heap finalReady.semantic
    fuel readFuel _ values results after.machine.heap requiredHeap done
    (SourceEqualitySelectedRequired.paths_nonnegative selected) finalReady.semantic finalValues
    (grows_refl _) support holds ambient terms, ?_⟩
  intro symbol pathsExist accepted
  exact SourceCurrentRequiredLanguage.requireAll_keep source after.machine.heap finalReady.semantic
    fuel readFuel _ values results after.machine.heap requiredHeap done
    (SourceEqualitySelectedRequired.paths_nonnegative selected) finalReady.semantic finalValues
    (grows_refl _) support holds ambient symbol terms accepted
    (selected_paths_exist trace (Term.node symbol terms) pathsExist)

end MicroCFTA.SourceCurrentClassRequired
