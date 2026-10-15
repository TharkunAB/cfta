import MicroCFTA.SourceCurrentClassRequired
import MicroCFTA.SourceCurrentRequiredEndpoints
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentRequiredQueryMemos

/-!
# Actual current scans and required execution ready for later equality work

The successful scan supplies the original selected classes and its exact
returned heap. Required execution derives every original selected path
domain, physical heap invariant, and completed global memo table there.
The same native state advances to the returned constructor heap. No table
is reset. Shared-target and class-edit execution remain separate steps.
-/
namespace MicroCFTA.SourceCurrentClassRequiredReady
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

/-- Actual successful scans derive finite exact required execution and every next-stage invariant. -/
theorem scan_required_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo none selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ scanMemos finalMemos results requiredHeap,
      SourceCurrentClassScanGlobalMemos.ScanReads trace memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results after.machine.heap requiredHeap scanMemos finalMemos ∧
      Valid requiredHeap finalMemos ∧ Extends scanMemos.unfolding finalMemos.unfolding ∧
      finalMemos.query = scanMemos.query ∧
      IdleReady top conjoin (advanceHeap after requiredHeap) ∧ CostHeap requiredHeap ∧ FieldHeap requiredHeap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver requiredHeap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      Keeps before.machine.heap requiredHeap ∧ Keeps after.machine.heap requiredHeap ∧
      SemanticReady requiredHeap ∧ Values requiredHeap values ∧ Values requiredHeap results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values after.machine.heap) results requiredHeap ∧
      SourceCurrentRequiredResultDomain.ForestDomain
        (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) results ∧
      (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) ∧
      ∀ holds ambient terms,
        (All₂ (meaning holds ambient) results terms ↔
          All₂ (meaning holds ambient) values terms ∧
            SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
        (∀ symbol, (∀ path ∈ classes.flatten, ∃ part, (Term.node symbol terms).atPath path = some part) →
          All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  obtain ⟨scanMemos, results, requiredHeap, reads, scanValid, scanReady, scanCosts, scanFields,
      scanCorrect, extension, _tips, kept, requiredKept, requiredSemantic, originalValues, resultValues,
      stable, domain, _maximal, language⟩ :=
    SourceCurrentClassRequired.scan_required_complete trace ready available costs fields proper
      formulas solver correct memos valid
  have stableRun := stable
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have scanValues : Values after.machine.heap values :=
    (SourceCurrentClassScanGlobalMemos.scan_memos trace ready available costs fields proper
      formulas solver correct memos valid).choose_spec.2.2.2.2.2.2.1
  have heapEffects := SourceCurrentRequiredHeapEffects.requireAll
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results after.machine.heap requiredHeap
    done scanReady.semantic scanCosts scanFields scanValues
  obtain ⟨finalMemos, requiredReads, finalValid, unfoldsRetained, querySame⟩ :=
    SourceCurrentRequiredQueryMemos.requireAll_memos fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values results after.machine.heap requiredHeap done scanReady.semantic scanCosts scanValues scanMemos scanValid
  have primary := SourceCurrentClassScanSupport.selected_primary trace ready available costs fields proper
    formulas solver correct memos valid
  have pathsClosed := SourceCurrentRequiredEndpoints.selected_paths_closed source reaches after.machine.heap
    scanReady.semantic (SourceEqualityExposureCosts.gate_ready scanReady.semantic scanCosts)
    selected values scanValues primary fuel readFuel results after.machine.heap requiredHeap done
    scanReady.semantic scanValues (grows_refl _)
  refine ⟨scanMemos, finalMemos, results, requiredHeap, reads, requiredReads, finalValid, unfoldsRetained,
    querySame, scanReady.advance requiredHeap requiredKept requiredSemantic,
    heapEffects.2.2.1, heapEffects.2.2.2.1,
    SourceCurrentEmptinessMemo.grows formulas solver requiredKept saved scanCorrect,
    extension, kept, requiredKept, requiredSemantic, originalValues, resultValues, stableRun,
    domain, ?_, language⟩
  intro path member
  obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
  exact pathsClosed path (List.mem_flatten.mpr ⟨paths, included, present⟩)
    (proper paths ((selected_sublist trace).subset included) path present)

end MicroCFTA.SourceCurrentClassRequiredReady
