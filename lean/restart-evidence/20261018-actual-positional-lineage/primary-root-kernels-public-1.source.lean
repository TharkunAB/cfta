import MicroCFTA.SourceCurrentPrimaryRootSupport
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 10000000

namespace MicroCFTA.PrimaryRootSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def positive : Guard := ⟨some [[[0],[1]]],.top⟩
private def tau : Syntax Symbol Guard := .binder false (.node [.mk ("pair",.top) plain [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("mixed",.top) positive [tau,tau]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def mu : Node := ((InternedProbeProvenance.children root)[0]?).getD .empty
private def tauBuilt := InternedFreshOrdinaryConstruction.build tau [] empty
private def first := SourceEqualityConstraintAllocation.construct positive.equalities Cache.emptyState
private def positiveValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | .error _ => .contradiction
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def plainValue : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial second.2
private def checked : SourceEqualityNativeDemand.State 4 :=
  ⟨SourceRecursiveIntersectionThunks.initial 4 ⟨heap,Cache.emptyState⟩,operations⟩
private def before := SourceCurrentAllocatedSharedTargetState.initial checked SourceCurrentMemoMergeGraph.empty
private def called := SourceCurrentAllocatedSharedEditWorker.head 8 mu before
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := called.state
private def row := ((nodeEdges root)[0]?).getD (run (makeEdge ("mixed",.top) positive [mu,mu]) heap).1

private theorem constructed : built = .done root heap := by
  obtain ⟨result, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]
private theorem first_done : first = (.ok positiveValue,first.2) := by cbv
private theorem second_done : second = (.ok plainValue,second.2) := by cbv
private theorem positive_cached : SourceEqualityGuardReadback.Cached positive.equalities := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized
    (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [positive,plain] :=
  SourceEqualityOriginalAllocationHistory.History.construct
    (SourceEqualityOriginalAllocationHistory.History.construct (.start Cache.emptyState) positive_cached first_done)
    SourceEqualityGuardReadback.empty_cached second_done
private theorem initial : SourceCurrentConjunctionClassScan.Ready checked ∧ Available heap root := by
  have produced := SourceCurrentConjunctionClassHistoryEntry.constructed 4 history Cache.empty_valid expression
    (fun guard member => by
      have included : guard = positive ∨ guard = plain := by
        simpa [expression,tau,SourceEqualityConstraintOrigins.guards,
          SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      rcases included with rfl | rfl
      · exact .head _
      · exact .tail _ (.head _)) root heap constructed
  exact ⟨produced.1,produced.2.1⟩
private theorem good : SourceCurrentNativeOperationHeap.Good checked :=
  SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.1.good) initial.1.semantic initial.1.costs
private theorem mu_available : Available heap mu :=
  initial.2.children mu (by cbv; exact .head _)
private theorem causal : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem plain_test : SourceMemoGate.plain plain = true := by
  simp [SourceMemoGate.plain,SourceCompactGuards.sourceEqualities,SourceCompactGuards.positiveNormalized,plain]
private theorem accepted : SourceMemoGate.unconstrained mu = true := by
  obtain ⟨value, state, done, _, annotated⟩ := SourceEqualityAnnotationConstruction.closed
    (fun guard : Guard => guard = plain) tau
    (by simp [tau,SourceEqualityAnnotationConstruction.Allowed,SourceEqualityAnnotationConstruction.ManyAllowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed])
  have tauDone : tauBuilt = .done mu tauBuilt.state := by cbv
  have same : value = mu := (InternedNestedConstruction.Outcome.done.inj (done.symm.trans tauDone)).1
  have annotatedMu : SourceEqualityAnnotationLanguage.Annotated (fun guard : Guard => guard = plain) mu := same ▸ annotated
  have translated : SourceEqualityAnnotationLanguage.Annotated Plain mu :=
    SourceCurrentHereditaryUnconstrained.annotated_mono
      (first := fun guard : Guard => guard = plain) (second := Plain)
      (fun guard same => by cases same; exact plain_test) annotatedMu
  exact SourceCurrentHereditaryUnconstrained.unconstrained mu translated
private theorem not_global_plain : ¬ SourceEqualityAnnotationHeap.Heap Plain heap := by
  intro annotation
  have member : row ∈ nodeEdges root := by cbv; exact .head _
  have resident := resident_edges heap good.heap.semantic.1.normal.facts.linked root initial.2.resident row member
  have guarded := annotation row.entry.key row resident
  have exactGuard : row.entry.key.constraint = positive := by cbv
  rw [exactGuard] at guarded
  have nonplain : SourceMemoGate.plain positive = false := by
    simp [SourceMemoGate.plain,SourceCompactGuards.sourceEqualities,SourceCompactGuards.positiveNormalized,positive]
  rw [nonplain] at guarded
  contradiction
private def values : List Node := [mu,.reference .depth]
private def paths : EqualityNormalize.Class := [[0],[0]]
private theorem primary_called : SourceCurrentAllocatedGateWorker.primary 1 values paths checked = .done false checked := by cbv
private theorem open_sibling : ¬ MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [values])
  cases impossible
private theorem witness :
    built = .done root heap ∧ SourceCurrentNativeOperationHeap.Good checked ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧ ¬ SourceEqualityAnnotationHeap.Heap Plain heap ∧
    Available heap mu ∧ SourceEqualityRequiredGraph.Recursive mu ∧
    ¬ MergedColdReaderClosedInputs.ClosedValues values ∧
    SourceCurrentAllocatedGateWorker.primary 1 values paths checked = .done false checked ∧
    SourceCurrentActualRequiredRowOrigins.Root mu ∧
    SourceCurrentRequiredRowOrigins.ExposureSafe (.node [(0,.node [])]) mu ∧
    SourceCurrentActualRequiredRowOrigins.Root mu := by
  have rootFromPrimary := SourceCurrentPrimaryRootSupport.primary primary_called
    (show 0 :: [] ∈ paths by simp [paths]) (show values[0]? = some mu by rfl)
  have safe : SourceCurrentRequiredRowOrigins.ExposureSafe (.node [(0,.node [])]) mu :=
    .accepted _ _ accepted
  exact ⟨constructed,good,causal,not_global_plain,mu_available,by cbv,open_sibling,
    primary_called,rootFromPrimary,safe,SourceCurrentPrimaryRootSupport.exposure safe (by simp)⟩

/-- A real false primary selects the same productive Mu twice beside an unrelated open reference. -/
theorem duplicate_selected_mu :
    built = .done root heap ∧ SourceCurrentNativeOperationHeap.Good checked ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧ ¬ SourceEqualityAnnotationHeap.Heap Plain heap ∧
    Available heap mu ∧ SourceEqualityRequiredGraph.Recursive mu ∧
    ¬ MergedColdReaderClosedInputs.ClosedValues values ∧
    SourceCurrentAllocatedGateWorker.primary 1 values paths checked = .done false checked ∧
    SourceCurrentActualRequiredRowOrigins.Root mu ∧
    SourceCurrentRequiredRowOrigins.ExposureSafe (.node [(0,.node [])]) mu ∧
    SourceCurrentActualRequiredRowOrigins.Root mu := witness

end MicroCFTA.PrimaryRootSupportKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.PrimaryRootSupportKernels.duplicate_selected_mu
#print MicroCFTA.PrimaryRootSupportKernels.duplicate_selected_mu
#print axioms MicroCFTA.PrimaryRootSupportKernels.duplicate_selected_mu
