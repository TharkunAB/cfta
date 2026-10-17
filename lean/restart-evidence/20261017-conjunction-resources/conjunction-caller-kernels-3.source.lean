import MicroCFTA.SourceCurrentConjunctionExposureResources
import MicroCFTA.SourceCurrentConjunctionRequirementNumeric
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ConjunctionCallerResourceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def top : Guard := SourceEqualityConstraintConstructors.top
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("loop", .top) top [.var 0], .mk ("leaf", .top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("parent", .top) annotation [recursive, recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Value Symbol Guard := (children root)[0]?.getD .empty
private def parentRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges root)[0]?.getD
  (run (makeEdge ("unused", .top) top []) empty).1
private def first := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def firstValue : SourceEqualityConstraintAllocation.Value := match first.1 with
  | .ok value => value | .error _ => .contradiction
private def last := SourceEqualityConstraintAllocation.construct top.equalities first.2
private def lastValue : SourceEqualityConstraintAllocation.Value := match last.1 with
  | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial last.2
private def physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula := ⟨heap, operations⟩
private theorem annotation_cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem top_cached : SourceEqualityGuardReadback.Cached top.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 1 [] = .normalized [] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState last.2 [annotation, top] := by
  have firstDone : first = (.ok firstValue, first.2) := by cbv
  have lastDone : last = (.ok lastValue, last.2) := by cbv
  exact .construct (.construct (.start Cache.emptyState) annotation_cached firstDone) top_cached lastDone
private theorem constructed : built = .done root heap := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, Outcome.state]
private theorem covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [annotation, top] := by
  intro guard member
  simpa only [expression, recursive, SourceEqualityConstraintOrigins.guards, SourceEqualityConstraintOrigins.edgeGuards,
    SourceEqualityConstraintOrigins.childGuards, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_self] using member
private theorem initial : SourceCurrentConjunctionClassScan.Ready
    (⟨SourceRecursiveIntersectionThunks.initial 0 ⟨heap, Cache.emptyState⟩, operations⟩ : SourceEqualityNativeDemand.State 0) ∧
    Available heap root ∧ root.free = [] ∧ SourceRecursiveIntersectionInputView.Original root :=
  SourceCurrentConjunctionClassHistoryEntry.constructed 0 history Cache.empty_valid expression covered root heap constructed
private theorem ready : SourceCurrentConjunctionRowsAllocation.Ready physical :=
  SourceCurrentAllocatedConjunctionMemo.ready _ initial.1.good initial.1.semantic initial.1.costs
private theorem child_available : Available heap child :=
  initial.2.1.children child (by cbv; exact .head _)
private theorem child_closed : child.free = [] := by cbv
private theorem child_mu : ∃ entry body depth ordinary, child = .mu entry body depth ordinary := by
  have kind : (match child with | .mu .. => True | _ => False) := by cbv
  cases found : child with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [found] at kind
private def q := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)
private theorem fits : Fits q heap := SourceCurrentMemoMergeResourceControl.initial heap _
  (InternedValueMassHeap.initial heap initial.1.good.native.machine.1)
private theorem duplicated_available : Values heap [child, child] := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  exact member ▸ child_available
private theorem duplicated_closed : ClosedValues [child, child] := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  exact member ▸ child_closed

/-- Actual field history and source construction produce duplicate recursive exposures with original-count padding. -/
theorem constructed_exposure :
    (∃ entry body depth ordinary, child = .mu entry body depth ordinary) ∧
    ∃ rows after, SourceCurrentConjunctionCompletionReads.Exposures [child, child] heap rows after ∧
      SourceCurrentConjunctionRowsAllocation.Ready ⟨after, operations⟩ ∧
      SourceCurrentConjunctionRowsAllocation.Effects physical ⟨after, operations⟩ ∧
      Fits (SourceCurrentConjunctionExposureResources.forecast 4 q) after ∧ rows.length = 2 ∧
      (∀ row ∈ rows, row.length ≤ SourceCurrentConjunctionExposureResources.forecast 4 q ∧ Edges after row ∧ ClosedEdges row) ∧
      (∀ fuel, SourceCurrentProjectionUnionResources.readFuel
          (SourceCurrentConjunctionExposureResources.forecast 4 q) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel [child, child] physical = .done rows ⟨after, operations⟩) := by
  exact ⟨child_mu, SourceCurrentConjunctionExposureResources.complete [child, child] physical 4 q ready
    duplicated_available duplicated_closed fits (by decide)⟩

end MicroCFTA.ConjunctionCallerResourceKernels
#print axioms MicroCFTA.ConjunctionCallerResourceKernels.constructed_exposure
#check @MicroCFTA.ConjunctionCallerResourceKernels.constructed_exposure
#print MicroCFTA.ConjunctionCallerResourceKernels.constructed_exposure
