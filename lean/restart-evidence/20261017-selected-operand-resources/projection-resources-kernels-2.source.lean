import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ProjectionResourceIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open InternedStoredShallowCompletion (BinderFree)
open SourceCurrentAllocatedRecursiveMassTrace (ceiling charge massAfter credit)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "initialBound" => InternedValueMassHeap.initialBound

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0, .var 1, .var 2]])]])

private theorem initial :
    ∃ input source, InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Available source input ∧
      InternedFreshOrdinaryContext.Context source [.reference (.intersection 3 5)] ∧
      InternedFreshOrdinaryDepthHeap.Heap source ∧ InternedRecordCoherence.Covered [] source := by
  have literal : Available (empty : State Nat Bool) (.reference (.intersection 3 5)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection 3 5 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection 3 5) literal
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection 3 5] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source at built
  have checked := InternedFreshOrdinaryFacts.build_verified expression _ empty empty_facts context.inputs
  have contexts : InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state
      [.reference (.intersection 3 5)] := context.build expression
  have depths : InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state :=
    (InternedRecordDepthExecution.build_depth expression _ empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  refine ⟨input, source, built, checked.result input source built,
    by simpa only [built, Outcome.state] using contexts,
    by simpa only [built, Outcome.state] using depths, ?_⟩
  exact InternedFreshOrdinaryCoverage.build_covered expression _ empty empty_valid InternedRecordCoherence.empty_correct.2 input source built

private theorem observed : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done input _ => Reference.intersection 3 5 ∈ input.free ∧
        ¬ BinderFree (encode (leaves input) [] input) ∧
        (match input with | .mu _ body _ _ => ¬ BinderFree (encode (leaves body) [] body) | _ => False) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv
  simp
  exact .head _


/-- Own open nested construction produces bounded first unfolding and exact full-state warm replay. -/
theorem nested_unfold_warm :
    ∃ input source result after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Reference.intersection 3 5 ∈ input.free ∧
      (∃ entry body level ordinary, input = .mu entry body level ordinary ∧ ¬ PreparedWithoutMu body) ∧
      unfold input source = .done result after ∧ unfold input after = .done result after ∧
      Stored (ceiling (initialBound source)) after ∧
      Stored (ceiling (ceiling (initialBound source))) after ∧
      InternedValueMass.value result ≤ ceiling (initialBound source) ∧
      after.nodes.next ≤ source.nodes.next + charge (initialBound source) ∧
      after.edges.next ≤ source.edges.next + charge (initialBound source) := by
  obtain ⟨input, source, built, available, context, depth, covered⟩ := initial
  have shape := observed
  rw [built] at shape
  dsimp only at shape
  have nested : ∃ entry body level ordinary, input = .mu entry body level ordinary ∧ ¬ PreparedWithoutMu body := by
    cases input with
    | mu entry body level ordinary =>
      refine ⟨entry, body, level, ordinary, rfl, ?_⟩
      intro prepared
      exact shape.2.2 (InternedStoredClosedMuCompletion.encode_withoutMu (leaves body) [] body prepared)
    | empty | reference | node | union => cases shape.2.2
  have initialStored := InternedValueMassHeap.initial source context.normal.facts
  obtain ⟨result, after, done, _context, _depth, _covered, _available, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded input source context available depth covered
  have first := SourceCurrentAllocatedProjectionResources.unfold_bound input source _ initialStored available
  have stored : Stored (ceiling (initialBound source)) after := by simpa only [done, Outcome.state] using first.1
  have warm := InternedFreshOrdinaryStoredSubstitution.unfold_replay input source after result after
    context.normal.facts.coherent.valid done (grows_refl _)
  have repeated := SourceCurrentAllocatedProjectionResources.unfold_bound input after _ stored
    (available.grows source after growth history)
  refine ⟨input, source, result, after, built, shape.1, nested, done, warm, stored,
    ?_, first.2.2.2 result after done, ?_, ?_⟩
  · simpa only [warm, Outcome.state] using repeated.1
  · simpa only [done, Outcome.state] using first.2.1
  · simpa only [done, Outcome.state] using first.2.2.1

private def productive : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [], .mk 1 false [.var 0]])

private theorem productive_shape : match InternedFreshOrdinaryConstruction.build productive [] empty with
    | .pending .. => False
    | .done input _ => input.free = [] ∧
      (∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = []) := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨rfl, _, _, _, _, rfl, _, .head _, rfl, rfl⟩

/-- A productive recursive source constructs its own complete row read and all same-return bounds. -/
theorem productive_read :
    ∃ input source fuel rows after,
      InternedFreshOrdinaryConstruction.build productive [] empty = .done input source ∧
      (∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = []) ∧
      MergedFreshOrdinaryExposure.nodeEdges fuel input source = .done rows after ∧
      Stored (massAfter (fuel + 1) (initialBound source)) after ∧
      after.nodes.next ≤ source.nodes.next + credit (fuel + 1) (initialBound source) ∧
      after.edges.next ≤ source.edges.next + credit (fuel + 1) (initialBound source) ∧
      rows.length ≤ (fuel + 1) * massAfter (fuel + 1) (initialBound source) ∧
      InternedNestedProvenance.Edges after rows := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete productive
  have checked := InternedFreshOrdinaryFacts.build_verified productive [] empty empty_facts (by simp [InternedNestedProvenance.Values])
  have available := checked.result input source built
  have semantic := SourceEqualityRequiredSemanticCache.constructed productive input source built
  have shape := productive_shape
  rw [built] at shape
  dsimp only at shape
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  obtain ⟨fuel, rows, after, read, _semantic, _covered, _heap, _growth, _history, _resident, _closed, _stable⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed input source semantic.ready.semantic semantic.ready.covered
      semantic.ready.depth available shape.1
  have resources := SourceCurrentAllocatedProjectionResources.read_bound fuel input source semantic.ready.semantic
    semantic.ready.covered available shape.1 _ stored rows after read
  exact ⟨input, source, fuel, rows, after, built, shape.2, read, resources⟩

end MicroCFTA.ProjectionResourceIntegration

#print axioms MicroCFTA.ProjectionResourceIntegration.nested_unfold_warm
#check @MicroCFTA.ProjectionResourceIntegration.nested_unfold_warm

#print axioms MicroCFTA.ProjectionResourceIntegration.productive_read
#check @MicroCFTA.ProjectionResourceIntegration.productive_read
