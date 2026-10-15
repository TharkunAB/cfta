import MicroCFTA.SourceSecondaryGateHead
import MicroCFTA.SourceEqualityAnnotationExposure

/-!
# Physical annotations through heads after clear secondary gates

A finite warm head chain supplies actual same-heap Mu unfolding equations.
Each unfolding retains resident physical constraints. Closed stopping points
use the existing bounded annotation theorem. Actual row reads and ordinary
reconstruction therefore preserve the initial annotation predicate. The
proof does not require original closedness, a cost heap, or a final heap
premise.
-/
namespace MicroCFTA.SourceSecondaryGateHeadHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open MergedSourceExposure (Result)
open MergedFreshOrdinaryExposure
open SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open SourceEqualityAnnotationHeap (Heap)
open SourceSecondaryGateHead (WarmHead)

private theorem unfolded_inputs (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {value next : Value Symbol Guard} {state : State Symbol Guard}
    (semantic : SemanticReady state) (available : Available state value) (heap : Heap annotation state)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value state = .done next state) :
    Available state next ∧ Heap annotation state := by
  have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap annotation value state
    semantic.ready.semantic.1.normal.facts heap available
  have afterHeap : Heap annotation state := by
    simpa only [InternedFreshOrdinaryConstraintHeap.Heap, Heap, actual, Outcome.state] using retained
  obtain ⟨result, after, done, _, _, resultAvailable, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete value state semantic available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
  cases sameValue
  cases sameState
  exact ⟨resultAvailable, afterHeap⟩

private theorem collect_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) (heap : Heap annotation state)
    (seen : List Nat) (fuel : Nat) : Heap annotation (collect fuel state seen [value]).state := by
  revert fuel seen heap available semantic
  induction support with
  | empty =>
      intro _ _ heap seen fuel
      cases fuel <;> simpa only [collect, Result.prepend, Result.state] using heap
  | ordinary =>
      intro _ _ heap seen fuel
      cases fuel <;> simpa only [collect, Result.prepend, Result.state] using heap
  | closed closed =>
      intro semantic available heap seen fuel
      exact SourceEqualityAnnotationExposure.collect_heap annotation fuel _ semantic.ready.semantic
        semantic.ready.covered heap seen [_]
        (by intro child member; simpa only [List.mem_singleton.mp member] using available)
        (by intro child member; simpa only [List.mem_singleton.mp member] using closed)
  | @unfold entry body depth ordinary next actual rest ih =>
      intro semantic available heap seen fuel
      cases fuel with
      | zero => exact heap
      | succ fuel =>
          by_cases visited : entry.identity ∈ seen
          · simpa only [collect, ite_eq_left visited, Result.state] using heap
          · have inputs := unfolded_inputs annotation semantic available heap actual
            simpa only [collect, ite_eq_right visited, actual] using
              ih semantic inputs.1 inputs.2 (entry.identity :: seen) fuel

private theorem nodeEdges_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) (heap : Heap annotation state)
    (fuel : Nat) : Heap annotation (nodeEdges fuel value state).state := by
  cases support with
  | empty | ordinary => exact heap
  | closed closed =>
      exact SourceEqualityAnnotationExposure.nodeEdges_heap annotation fuel _ _ semantic.ready.semantic
        semantic.ready.covered heap available closed
  | @unfold entry body depth ordinary next actual rest =>
      have fallback : Heap annotation (collect fuel state [] [.mu entry body depth ordinary]).canonical.state := by
        rw [SourceEqualityAnnotationExposure.canonical_state]
        exact collect_heap annotation (.unfold actual rest) semantic available heap [] fuel
      cases next with
      | node => simpa only [nodeEdges, actual, Result.state] using heap
      | empty | reference | union | mu => simpa only [nodeEdges, actual] using fallback

/-- An actual completed warm-head reconstruction preserves its initial physical annotation predicate. -/
theorem warm_head_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {caller after : State Symbol Guard} {value result : Value Symbol Guard}
    (support : WarmHead caller value) (callerSemantic : SemanticReady caller)
    (callerAvailable : Available caller value) (fields : Heap annotation caller)
    (actual : Head value caller result after) : Heap annotation after := by
  cases actual with
  | read fuel edges middle read built =>
      have retained := nodeEdges_heap annotation support callerSemantic callerAvailable fields fuel
      have middleHeap : Heap annotation middle := by simpa only [read, Result.state] using retained
      have rebuilt := SourceEqualityAnnotationHeap.run annotation _
        (SourceEqualityAnnotationHeap.makeNode annotation edges) middle middleHeap
      simpa only [built] using rebuilt

/-- A false gate and current caller inputs derive annotation preservation for the actual later head. -/
theorem head_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path}
    {value result : Value Symbol Guard} {before final caller after : State Symbol Guard}
    (gate : InternedFreshOrdinaryStatefulGateTrace.NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value) (growth : Grows final caller)
    (fields : Heap annotation caller) (actual : Head value caller result after) : Heap annotation after :=
  warm_head_heap annotation (SourceSecondaryGateHead.warm_head gate semantic available caller growth)
    callerSemantic callerAvailable fields actual

end MicroCFTA.SourceSecondaryGateHeadHeap
