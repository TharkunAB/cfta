import MicroCFTA.SourceCurrentAllocatedRecursiveMassCheckedSeries

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MassCheckedSeriesIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedFreshOrdinaryContext (Context)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
local instance : DecidableEq Guard := fun ⟨firstEqualities, firstGuard⟩ ⟨secondEqualities, secondGuard⟩ =>
  decidable_of_iff (firstEqualities = secondEqualities ∧ firstGuard = secondGuard) (by simp)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Source" => InternedConstructorTemplates.State Symbol Guard
local notation "Series" => SourceCurrentAllocatedRecursiveMassSeries.run
local notation "code" => SourceCurrentAllocatedRecursiveMassCheckedSeries.code
local notation "replaceHeap" => SourceCurrentAllocatedRecursiveMassCheckedSeries.replaceHeap
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassSeries.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassSeries.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "Stored" => InternedValueMassHeap.Stored

/-- Two checked calls construct their source returns and retain the same populated tables and initial numeric credit. -/
theorem two_calls_exact (keysFirst keysSecond : Nat × Nat) (body : Value Symbol Guard)
    (before : Checked width) (good : Good before)
    (context : Context before.native.machine.heap environment)
    (available : Available before.native.machine.heap body)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap before.native.machine.heap)
    (covered : InternedRecordCoherence.Covered [] before.native.machine.heap) :
    ∃ first result middle after,
      SourceRecursiveIntersectionMaybeMu.maybeMu keysFirst body before.native.machine.heap = .done first middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu keysSecond first middle = .done result after ∧
      Trace 2 (.code (code [keysFirst, keysSecond] body)) before
        (.code (.pure result)) (replaceHeap before after) ∧
      SourceEqualityNativeDemand.execute 3 (.code (code [keysFirst, keysSecond] body)) before =
        .done result (replaceHeap before after) ∧
      Good (replaceHeap before after) ∧
      Stored (massAfter 2 (initialBound before.native.machine.heap)) after ∧
      after.nodes.next ≤ before.native.machine.heap.nodes.next + credit 2 (initialBound before.native.machine.heap) ∧
      after.edges.next ≤ before.native.machine.heap.edges.next + credit 2 (initialBound before.native.machine.heap) ∧
      (replaceHeap before after).native.nodes = before.native.nodes ∧
      (replaceHeap before after).native.edges = before.native.edges ∧
      (replaceHeap before after).native.machine.domains = before.native.machine.domains ∧
      (replaceHeap before after).operations = before.operations ∧ Available after result := by
  obtain ⟨result, after, actual, finalGood, stored, nodes, edges, _context, _heap, _covered, output⟩ :=
    SourceCurrentAllocatedRecursiveMassCheckedSeries.complete [keysFirst, keysSecond] body before
      good context available depthHeap covered
  obtain ⟨sourceResult, sourceAfter, sourceDone, _sourceContext, _sourceHeap, _sourceCovered, _sourceOutput⟩ :=
    SourceCurrentAllocatedRecursiveMassSeries.finish [keysFirst, keysSecond] body before.native.machine.heap
      context available depthHeap covered
  have sourceActual := SourceCurrentAllocatedRecursiveMassCheckedSeries.trace [keysFirst, keysSecond]
    body before sourceResult sourceAfter context.normal.facts available sourceDone
  have exactReturn := (SourceEqualityNativeDemand.Steps.execute _ _ _ _ _ sourceActual.steps).symm.trans
    (SourceEqualityNativeDemand.Steps.execute _ _ _ _ _ actual.steps)
  have finalState := (SourceEqualityNativeDemand.Outcome.yielded.inj exactReturn).2
  have finalControl := (SourceEqualityNativeDemand.Outcome.yielded.inj exactReturn).1
  have sameValue : sourceResult = result := by cases finalControl; rfl
  have sameHeap : sourceAfter = after := congrArg (fun state => state.native.machine.heap) finalState
  subst sourceResult
  subst sourceAfter
  have completed : SourceEqualityNativeDemand.execute 3 (.code (code [keysFirst, keysSecond] body)) before =
      .done result (replaceHeap before after) := by
    change SourceEqualityNativeDemand.execute (2 + 1) _ _ = _
    have yielded : SourceEqualityNativeDemand.execute 2 (.code (code [keysFirst, keysSecond] body)) before =
        .yielded (.code (.pure result)) (replaceHeap before after) :=
      SourceEqualityNativeDemand.Steps.execute _ _ _ _ _ actual.steps
    rw [SourceEqualityNativeDemand.execute_add, yielded]
    rfl
  cases firstCall : SourceRecursiveIntersectionMaybeMu.maybeMu keysFirst body before.native.machine.heap with
  | pending key current =>
      simp only [SourceCurrentAllocatedRecursiveMassSeries.run, firstCall, Outcome.bind] at sourceDone
      cases sourceDone
  | done first middle =>
      cases secondCall : SourceRecursiveIntersectionMaybeMu.maybeMu keysSecond first middle with
      | pending key current =>
          simp only [SourceCurrentAllocatedRecursiveMassSeries.run, firstCall, secondCall, Outcome.bind] at sourceDone
          cases sourceDone
      | done value final =>
          have same : Outcome.done value final = Outcome.done result after := by
            simpa only [SourceCurrentAllocatedRecursiveMassSeries.run, firstCall, secondCall, Outcome.bind] using sourceDone
          cases same
          have tables := SourceCurrentAllocatedRecursiveMassCheckedSeries.same_tables before after
          exact ⟨first, result, middle, after, rfl, rfl, actual, completed, finalGood,
            stored, nodes, edges, tables.1, tables.2.1, tables.2.2.1, tables.2.2.2, output⟩

private def fixture : Syntax Symbol Guard :=
  .binder false (.node [.mk ("outer", .top) SourceEqualityConstraintConstructors.top [.var 0,
    .binder false (.node [.mk ("inner", .top) SourceEqualityConstraintConstructors.top
      [.var 0, .var 1, .var 2, .var 3]])]])

private def captures : List (Value Symbol Guard) :=
  [.reference (.intersection 3 5), .reference (.intersection 7 11)]

/-- A source-built open nested Mu supplies both used names before any checked call or later-entry resource premise. -/
theorem constructed_nested_checked :
    ∃ body source,
      InternedFreshOrdinaryConstruction.build fixture captures empty = .done body source ∧
      Reference.intersection 3 5 ∈ body.free ∧ Reference.intersection 7 11 ∈ body.free ∧
      (match body with | .mu .. => True | _ => False) ∧
      ∀ (before : Checked width), before.native.machine.heap = source → Good before →
        ∃ first result middle after,
          SourceRecursiveIntersectionMaybeMu.maybeMu (3, 5) body source = .done first middle ∧
          SourceRecursiveIntersectionMaybeMu.maybeMu (7, 11) first middle = .done result after ∧
          Trace 2 (.code (code [(3, 5), (7, 11)] body)) before
            (.code (.pure result)) (replaceHeap before after) ∧
          Good (replaceHeap before after) ∧
          Stored (massAfter 2 (initialBound source)) after ∧
          after.nodes.next ≤ source.nodes.next + credit 2 (initialBound source) ∧
          after.edges.next ≤ source.edges.next + credit 2 (initialBound source) ∧
          (replaceHeap before after).native.nodes = before.native.nodes ∧
          (replaceHeap before after).native.edges = before.native.edges ∧
          (replaceHeap before after).native.machine.domains = before.native.machine.domains ∧
          (replaceHeap before after).operations = before.operations ∧ Available after result := by
  have literal (pair : Nat × Nat) : Available (empty : Source) (.reference (.intersection pair.1 pair.2)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection pair.1 pair.2 := List.mem_singleton.mp member
      cases impossible)
  have context := (InternedFreshOrdinaryContext.empty_context.local (.intersection 7 11) (literal (7, 11))).local
    (.intersection 3 5) (literal (3, 5))
  obtain ⟨body, source, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete fixture
    [.intersection 3 5, .intersection 7 11] empty context InternedFreshOrdinaryDepthHeap.empty_heap
    InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build fixture captures empty = .done body source at built
  have available := (InternedFreshOrdinaryFacts.build_verified fixture captures empty empty_facts context.inputs).result body source built
  have nextContext := context.build fixture
  change Context (InternedFreshOrdinaryConstruction.build fixture captures empty).state captures at nextContext
  have nextDepth := (InternedRecordDepthExecution.build_depth fixture captures empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have covered := InternedFreshOrdinaryCoverage.build_covered fixture captures empty empty_valid
    InternedRecordCoherence.empty_correct.2 body source built
  have used : (match InternedFreshOrdinaryConstruction.build fixture captures empty with
      | .done value _ => decide (Reference.intersection 3 5 ∈ value.free ∧ Reference.intersection 7 11 ∈ value.free) ∧
          (match value with | .mu .. => True | _ => False)
      | .pending _ _ => False) := by
    set_option cbv.maxSteps 200000000 in cbv
  rw [built] at used
  have names : Reference.intersection 3 5 ∈ body.free ∧ Reference.intersection 7 11 ∈ body.free := by
    simpa only [decide_eq_true_eq] using used.1
  refine ⟨body, source, built, names.1, names.2, used.2, ?_⟩
  intro before sameHeap good
  have sourceContext : Context source captures := by simpa only [built, Outcome.state] using nextContext
  have sourceDepth : InternedFreshOrdinaryDepthHeap.Heap source := by simpa only [built, Outcome.state] using nextDepth
  obtain ⟨first, result, middle, after, firstCall, secondCall, actual, _complete, finalGood,
      stored, nodes, edges, tables⟩ := two_calls_exact (3, 5) (7, 11) body before good
    (by simpa only [sameHeap] using sourceContext) (by simpa only [sameHeap] using available)
    (by simpa only [sameHeap] using sourceDepth) (by simpa only [sameHeap] using covered)
  exact ⟨first, result, middle, after, by simpa only [sameHeap] using firstCall, secondCall,
    actual, finalGood, by simpa only [sameHeap] using stored, by simpa only [sameHeap] using nodes,
    by simpa only [sameHeap] using edges, tables⟩

#print axioms two_calls_exact
#check @two_calls_exact
#print axioms constructed_nested_checked
#check @constructed_nested_checked
end MicroCFTA.MassCheckedSeriesIndependent
