import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.InternedGuardedBudgetStoredExecution
import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap

/-!
# Ordinary head reconstruction for open recursive records

A single stored unfolding can expose ordinary rows while other children
retain free references. Actual ordinary reconstruction preserves their
independent language and the complete semantic cache. No input or output
closedness is required. Repeated recursive exposure and gate-to-path
correspondence remain separate obligations.
-/
namespace MicroCFTA.SourceEqualityOpenOrdinaryHead
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredCache SourceEqualityRequiredHead SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)

/-- Ordinary reconstruction retains residency and every semantic heap for open resident rows. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before edges) :
    Keeps before (run (makeNode edges) before).2 ∧
      SemanticReady (run (makeNode edges) before).2 ∧
      Available (run (makeNode edges) before).2 (run (makeNode edges) before).1 ∧
      Ordinary (run (makeNode edges) before).1 := by
  have facts := semantic.ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.node_verified edges before facts resident
  have ready : Ready (run (makeNode edges) before).2 :=
    ⟨SourceRecursiveIntersectionSemanticHeap.node edges before semantic.ready.semantic resident,
      InternedNestedCoverage.run_covered _ before facts.coherent.valid semantic.ready.covered,
      InternedOpenDepthReadback.preserve before _ semantic.ready.depth
        (InternedShallowHeap.makeNode_noNewMu edges before)⟩
  exact ⟨⟨ready, checked.growth, checked.history⟩,
    ⟨ready,
      InternedGuardedProbeHeap.preserve before _ semantic.guarded (InternedShallowHeap.makeNode_noNewMu edges before),
      InternedGuardedBudgetProbeHeap.preserve before _ semantic.budget (InternedShallowHeap.makeNode_noNewMu edges before)⟩,
    checked.result _ _ rfl, SourceEqualityRequiredCache.node_ordinary edges before facts resident⟩

/-- A single actual unfolding completes on any available record and retains its open independent language. -/
theorem unfold_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) :
    ∃ result after, InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after ∧
      Keeps before after ∧ SemanticReady after ∧ Available after result ∧
      ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term := by
  obtain ⟨result, after, done, context, decoded, covered, resultAvailable, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded value before semantic.ready.semantic.1
      available semantic.ready.semantic.2 semantic.ready.covered
  have depth := InternedStoredPlanBinderDepthProgress.unfold_heap value before semantic.ready.semantic.1
    semantic.ready.semantic.2 semantic.ready.depth available
  have guarded := InternedGuardedStoredExecution.unfold_checked value before semantic.ready.semantic.1
    semantic.guarded available
  have budget := InternedGuardedBudgetStoredExecution.unfold_heaps value before semantic.ready.semantic.1
    semantic.budget semantic.ready.semantic.2 available
  have ready : Ready after := ⟨⟨context, decoded⟩, covered, by simpa only [done, Outcome.state] using depth⟩
  refine ⟨result, after, done, ⟨ready, growth, history⟩,
    ⟨ready, ?_, ?_⟩, resultAvailable, ?_⟩
  · simpa only [done, Outcome.state] using guarded.heap
  · simpa only [done, Outcome.state] using budget.1
  · intro holds ambient term
    exact (congrFun (guarded.result result after done holds ambient) term).to_iff

/-- An actual ordinary unfolding reconstructs the source head with exact open language and returned cache. -/
theorem ordinary [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before middle : State Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (semantic : SemanticReady before) (available : Available before value)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle) :
    Head value before (run (makeNode edges) middle).1 (run (makeNode edges) middle).2 ∧
      Keeps before (run (makeNode edges) middle).2 ∧
      SemanticReady (run (makeNode edges) middle).2 ∧
      Available (run (makeNode edges) middle).2 (run (makeNode edges) middle).1 ∧
      Ordinary (run (makeNode edges) middle).1 ∧
      ∀ holds ambient term,
        meaning holds ambient (run (makeNode edges) middle).1 term ↔ meaning holds ambient value term := by
  obtain ⟨actual, after, done, keeps, middleSemantic, actualAvailable, language⟩ :=
    unfold_complete value before semantic available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans unfolded)
  cases sameValue
  cases sameState
  have resident := InternedEdgeResidency.resident_edges middle
    middleSemantic.ready.semantic.1.normal.facts.linked _ actualAvailable.resident
  have rebuilt := node edges middle middleSemantic resident
  refine ⟨ordinary_fast value before middle entry edges depth free recursive unfolded,
    keeps.trans rebuilt.1, rebuilt.2.1, rebuilt.2.2.1, rebuilt.2.2.2, ?_⟩
  intro holds ambient term
  have laws := InternedGuardedLanguage.laws holds ambient
  exact (MergedColdInterpretation.makeNode_exact middle middleSemantic.ready.semantic.1.normal.facts
    (meaning holds ambient) edges resident holds laws term).trans
    ((laws.node entry edges depth free term).symm.trans (language holds ambient term))

/-- Every completed head receipt agrees with the exact open ordinary reconstruction. -/
theorem verified [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (semantic : SemanticReady before) (available : Available before value)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ Ordinary result ∧
      ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term := by
  have actual := ordinary value before middle entry edges depth free semantic available recursive unfolded
  obtain ⟨sameValue, sameState⟩ := actual.1.unique trace
  cases sameValue
  cases sameState
  exact actual.2

/-- Open ordinary reconstruction retains every physical edge-annotation predicate. -/
theorem ordinary_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (value : Value Symbol Guard) (before middle : State Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (semantic : SemanticReady before) (available : Available before value)
    (heap : InternedFreshOrdinaryConstraintHeap.Heap property before)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle) :
    InternedFreshOrdinaryConstraintHeap.Heap property (run (makeNode edges) middle).2 := by
  have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property value before
    semantic.ready.semantic.1.normal.facts heap available
  have middleHeap : InternedFreshOrdinaryConstraintHeap.Heap property middle := by
    simpa only [unfolded, Outcome.state] using retained
  exact InternedFreshOrdinaryConstraintHeap.node_heap property edges middle middleHeap

end MicroCFTA.SourceEqualityOpenOrdinaryHead
