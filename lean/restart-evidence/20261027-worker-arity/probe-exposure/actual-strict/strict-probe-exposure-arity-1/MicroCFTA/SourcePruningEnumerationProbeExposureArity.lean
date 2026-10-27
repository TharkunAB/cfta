import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Edge-record arity through actual cold exposure

Stored reconstruction preserves every old and newly stored edge key.
Each actual done or pending outcome retains its complete cache.
The bounded reader also retains unresolved and exhausted endpoints.
No closed input or successful future read is supplied.
-/
namespace MicroCFTA.SourcePruningEnumerationProbeExposureArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}

private theorem unfold_verified [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) :
    Verified state (InternedFreshOrdinaryStoredSubstitution.unfold value state) Available := by
  cases value with
  | empty | reference | node | union => exact pure_verified state facts _ Available available
  | mu entry body depth ordinary =>
      apply InternedFreshOrdinaryFacts.build_verified _ _ state facts
      apply InternedStoredSubstitution.inputs_available body _ state
        (available.children body (by simp [children]))
      intro name replacement found
      simp only [] at found
      split at found
      · cases found; exact available
      · contradiction

/-- Every actual bounded worklist retains arity at its exact done, pending, unresolved or exhausted cache. -/
theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (facts : Facts state) (heap : Heap state)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    Heap (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state facts heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state facts heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts heap seen rest restInputs
              · have verified := unfold_verified (.mu entry body depth ordinary) state facts available
                have retained := SourcePruningEnumerationArityOrigins.unfold_heap
                  (.mu entry body depth ordinary) state facts heap available
                cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending key after =>
                    simpa only [collect, ite_eq_right visited, unfolded, Outcome.state, Result.state] using retained
                | done result after =>
                    have afterFacts : Facts after := by simpa only [unfolded, Outcome.state] using verified.facts
                    have afterHeap : Heap after := by simpa only [unfolded, Outcome.state] using retained
                    have nextInputs : Values after (result :: rest) := by
                      intro child member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact verified.result result after unfolded
                      · simpa only [unfolded, Outcome.state] using verified.available child (restInputs child member)
                    simpa only [collect, ite_eq_right visited, unfolded] using
                      ih after afterFacts afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Direct reads and closure fallback retain the entire actual edge-record arity heap. -/
theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (heap : Heap state) (available : Available state value) :
    Heap (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentFacts : Facts current)
      (currentHeap : Heap current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap fuel current currentFacts currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state facts heap _ available
  | mu entry body depth ordinary =>
      have verified := unfold_verified (.mu entry body depth ordinary) state facts available
      have retained := SourcePruningEnumerationArityOrigins.unfold_heap
        (.mu entry body depth ordinary) state facts heap available
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending key after =>
          simpa only [nodeEdges, unfolded, Outcome.state, Result.state] using retained
      | done result after =>
          have afterFacts : Facts after := by simpa only [unfolded, Outcome.state] using verified.facts
          have afterHeap : Heap after := by simpa only [unfolded, Outcome.state] using retained
          have rootAvailable : Available after (.mu entry body depth ordinary) := by
            simpa only [unfolded, Outcome.state] using verified.available _ available
          have closure := fallback after afterFacts afterHeap (.mu entry body depth ordinary) rootAvailable
          cases result with
          | node => simpa only [nodeEdges, unfolded, Result.state] using afterHeap
          | empty | reference | union | mu => simpa only [nodeEdges, unfolded] using closure

/-- The actual comparison-read spelling keeps the same heap at successful and failed outcomes. -/
theorem read_outcome_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (heap : Heap state) (available : Available state value) :
    Heap (MergedFreshOrdinaryExposure.read fuel value state).state := by
  have retained := nodeEdges_heap fuel value state facts heap available
  cases actual : nodeEdges fuel value state with
  | done rows after | unresolved name after | pending key after | exhausted after =>
      simpa only [MergedFreshOrdinaryExposure.read, actual, Result.state, MergedSourceComparison.Result.state] using retained

/-- A completed actual projection read retains arity at its own returned heap. -/
theorem read_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before edges after)
    (facts : Facts before) (available : Available before value) (heap : Heap before) : Heap after := by
  cases actual with
  | done fuel completed =>
      simpa only [completed, Result.state] using nodeEdges_heap fuel value before facts heap available

/-- The actual row reconstruction adds no edge record after its literal read. -/
theorem head_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (facts : Facts before) (available : Available before value) (heap : Heap before) : Heap after := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
      have middleHeap := read_heap (.done fuel exposed) facts available heap
      simpa only [rebuilt] using SourcePruningEnumerationArityOrigins.node_heap edges middle middleHeap

/-- Current checked readiness supplies the record facts for the exact bounded cold read. -/
theorem nodeEdges_heap_of_good
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) Guard)]
    {width : Nat} (fuel : Nat) (value : Value (SourceObservations.Label FullSyntax.Formula) Guard)
    (before : SourceEqualityNativeDemand.State width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (heap : Heap before.native.machine.heap) (available : Available before.native.machine.heap value) :
    Heap (nodeEdges fuel value before.native.machine.heap).state :=
  nodeEdges_heap fuel value before.native.machine.heap good.heap.semantic.1.normal.facts heap available

end MicroCFTA.SourcePruningEnumerationProbeExposureArity
