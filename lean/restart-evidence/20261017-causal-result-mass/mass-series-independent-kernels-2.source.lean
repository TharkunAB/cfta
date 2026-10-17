import MicroCFTA.SourceCurrentAllocatedRecursiveMassSeries

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace MicroCFTA.MassSeriesIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentAllocatedRecursiveMassSeries
open InternedBinderProtocol (Reference)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "mass" => InternedValueMass.value
local notation "maybeMu" => SourceRecursiveIntersectionMaybeMu.maybeMu
local notation "runSeries" => SourceCurrentAllocatedRecursiveMassSeries.run

private def fixture : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [.var 0, .var 1, .var 2]])

private def captures : List (Value Nat Bool) :=
  [.reference (.intersection 3 5), .reference (.intersection 7 11)]

private theorem initial :
    ∃ body middle,
      build fixture captures empty = .done body middle ∧
      Reference.intersection 3 5 ∈ body.free ∧ Reference.intersection 7 11 ∈ body.free ∧
      InternedFreshOrdinaryContext.Context middle captures ∧
      InternedFreshOrdinaryDepthHeap.Heap middle ∧
      InternedRecordCoherence.Covered [] middle ∧ Available middle body := by
  have literal (pair : Nat × Nat) : Available (empty : State Nat Bool) (.reference (.intersection pair.1 pair.2)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection pair.1 pair.2 := List.mem_singleton.mp member
      cases impossible)
  have context := (InternedFreshOrdinaryContext.empty_context.local (.intersection 7 11) (literal (7, 11))).local
    (.intersection 3 5) (literal (3, 5))
  obtain ⟨body, middle, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete fixture
    [.intersection 3 5, .intersection 7 11] empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change build fixture captures empty = .done body middle at built
  have available := (InternedFreshOrdinaryFacts.build_verified fixture captures empty empty_facts context.inputs).result body middle built
  have nextContext := context.build fixture
  change InternedFreshOrdinaryContext.Context (build fixture captures empty).state captures at nextContext
  have nextDepth := (InternedRecordDepthExecution.build_depth fixture captures empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have covered := InternedFreshOrdinaryCoverage.build_covered fixture captures empty empty_valid
    InternedRecordCoherence.empty_correct.2 body middle built
  have used : (match build fixture captures empty with
      | .done value _ => decide (Reference.intersection 3 5 ∈ value.free ∧ Reference.intersection 7 11 ∈ value.free)
      | .pending _ _ => false) = true := by
    set_option cbv.maxSteps 200000000 in cbv
  have names : Reference.intersection 3 5 ∈ body.free ∧ Reference.intersection 7 11 ∈ body.free := by
    simpa only [built, decide_eq_true_eq] using used
  exact ⟨body, middle, built, names.1, names.2,
    by simpa only [built, Outcome.state] using nextContext,
    by simpa only [built, Outcome.state] using nextDepth, covered, available⟩

private theorem run_append (keys rest : List (Nat × Nat)) (body : Value Nat Bool) (before : State Nat Bool) :
    runSeries (keys ++ rest) body before = (runSeries keys body before).bind (fun value after => runSeries rest value after) := by
  induction keys generalizing body before with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.cons_append, runSeries]
      cases first : maybeMu key body before with
      | pending key after => rfl
      | done value after => exact ih value after

/-- An open nested Mu source constructs two calls. The second call uses the first literal return. -/
theorem constructed_two :
    ∃ body first result middle afterFirst after,
      build fixture captures empty = .done body middle ∧
      Reference.intersection 3 5 ∈ body.free ∧ Reference.intersection 7 11 ∈ body.free ∧
      maybeMu (3, 5) body middle = .done first afterFirst ∧
      maybeMu (7, 11) first afterFirst = .done result after ∧
      runSeries [(3, 5), (7, 11)] body middle = .done result after ∧
      Stored (massAfter 2 (InternedValueMassHeap.initialBound middle)) after ∧
      after.nodes.next ≤ middle.nodes.next + credit 2 (InternedValueMassHeap.initialBound middle) ∧
      after.edges.next ≤ middle.edges.next + credit 2 (InternedValueMassHeap.initialBound middle) ∧
      mass result ≤ massAfter 2 (InternedValueMassHeap.initialBound middle) := by
  obtain ⟨body, middle, built, usedFirst, usedSecond, context, heap, covered, available⟩ := initial
  obtain ⟨result, after, done, _context, _heap, _covered, _available, stored, nodes, edges, bounded, _growth, _history⟩ :=
    complete [(3, 5), (7, 11)] body middle context available heap covered
  cases firstCall : maybeMu (3, 5) body middle with
  | pending key current => simp only [runSeries, firstCall, Outcome.bind] at done; cases done
  | done first afterFirst =>
      cases secondCall : maybeMu (7, 11) first afterFirst with
      | pending key current => simp only [runSeries, firstCall, secondCall, Outcome.bind] at done; cases done
      | done value final =>
          have same : Outcome.done value final = Outcome.done result after := by
            simpa only [runSeries, firstCall, secondCall, Outcome.bind] using done
          cases same
          exact ⟨body, first, result, middle, afterFirst, after, built, usedFirst, usedSecond,
            firstCall, secondCall, done, stored, nodes, edges, bounded⟩

/-- A two-call prefix and generated suffix use one initial credit, with no later-entry counter premise. -/
theorem constructed_credit :
    ∃ body prefixResult result middle afterPrefix after,
      build fixture captures empty = .done body middle ∧
      runSeries [(3, 5), (7, 11)] body middle = .done prefixResult afterPrefix ∧
      runSeries [(13, 17)] prefixResult afterPrefix = .done result after ∧
      runSeries [(3, 5), (7, 11), (13, 17)] body middle = .done result after ∧
      Stored (massAfter 3 (InternedValueMassHeap.initialBound middle)) after ∧
      massAfter 3 (InternedValueMassHeap.initialBound middle) =
        massAfter 1 (massAfter 2 (InternedValueMassHeap.initialBound middle)) ∧
      credit 3 (InternedValueMassHeap.initialBound middle) =
        credit 2 (InternedValueMassHeap.initialBound middle) +
          credit 1 (massAfter 2 (InternedValueMassHeap.initialBound middle)) ∧
      ∀ bits,
        middle.nodes.next + credit 3 (InternedValueMassHeap.initialBound middle) < 2 ^ bits →
        middle.edges.next + credit 3 (InternedValueMassHeap.initialBound middle) < 2 ^ bits →
        afterPrefix.nodes.next + credit 1 (massAfter 2 (InternedValueMassHeap.initialBound middle)) < 2 ^ bits ∧
        afterPrefix.edges.next + credit 1 (massAfter 2 (InternedValueMassHeap.initialBound middle)) < 2 ^ bits ∧
        after.nodes.next < 2 ^ bits ∧ after.edges.next < 2 ^ bits := by
  obtain ⟨body, middle, built, _usedFirst, _usedSecond, context, heap, covered, available⟩ := initial
  obtain ⟨prefixResult, afterPrefix, prefixDone, nextContext, nextHeap, nextCovered, nextAvailable,
      prefixStored, firstNodes, firstEdges, _firstSize, _growth, _history⟩ :=
    complete [(3, 5), (7, 11)] body middle context available heap covered
  obtain ⟨result, after, suffixDone, _context, _heap, _covered, _available⟩ :=
    finish [(13, 17)] prefixResult afterPrefix nextContext nextAvailable nextHeap nextCovered
  have suffix := run_bound [(13, 17)] prefixResult afterPrefix
    (massAfter 2 (InternedValueMassHeap.initialBound middle)) nextContext.normal.facts prefixStored nextAvailable
  simp only [suffixDone, Outcome.state] at suffix
  have commonMass := massAfter_add 2 1 (InternedValueMassHeap.initialBound middle)
  have commonCredit := credit_add 2 1 (InternedValueMassHeap.initialBound middle)
  have whole : runSeries [(3, 5), (7, 11), (13, 17)] body middle = .done result after := by
    change runSeries ([(3, 5), (7, 11)] ++ [(13, 17)]) body middle = _
    rw [run_append, prefixDone, Outcome.bind, suffixDone]
  refine ⟨body, prefixResult, result, middle, afterPrefix, after, built, prefixDone, suffixDone, whole,
    ?_, commonMass, commonCredit, ?_⟩
  · rw [commonMass]
    exact suffix.1
  · intro bits nodesRoom edgesRoom
    have laterNodes := suffix.2.1
    have laterEdges := suffix.2.2.1
    simp only [List.length_cons, List.length_nil] at laterNodes laterEdges
    simp only [List.length_cons, List.length_nil] at firstNodes firstEdges
    change credit 3 (InternedValueMassHeap.initialBound middle) =
      credit 2 (InternedValueMassHeap.initialBound middle) + credit 1 (massAfter 2 (InternedValueMassHeap.initialBound middle)) at commonCredit
    omega

end MicroCFTA.MassSeriesIndependent

#print axioms MicroCFTA.MassSeriesIndependent.constructed_two
#check @MicroCFTA.MassSeriesIndependent.constructed_two
#print axioms MicroCFTA.MassSeriesIndependent.constructed_credit
#check @MicroCFTA.MassSeriesIndependent.constructed_credit
