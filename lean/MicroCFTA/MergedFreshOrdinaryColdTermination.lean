import MicroCFTA.InternedMuDepthInventory
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Finite actual repaired cold collection with new Mu allocation

The budget counts unseen canonical Mu identities by decreasing body depth.
Structural pending work has the lowest priority. Actual closed unfolding
can add Mu only at lower degrees, so it consumes this finite vector.
-/
namespace MicroCFTA.MergedFreshOrdinaryColdTermination
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedBinderProtocol (NodeKey)
open InternedMuDepthInventory
open MergedColdReaderTermination (weight workWeight weight_positive workWeight_append)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedFreshOrdinaryExposure
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- The finite budget gives every Mu degree higher priority than structural pending work. -/
def measure (limit : Nat) (state : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard)) :
    Fin (limit + 1) → Nat := fun index => match index.val with
  | 0 => workWeight pending
  | degree + 1 => count state seen degree

local instance (limit : Nat) : WellFoundedRelation (Fin limit → Nat) :=
  ⟨HeightOrder.VectorBelow limit, HeightOrder.vector_wellFounded limit⟩

/-- A structural reader step decreases the budget when it only adds visited identities. -/
theorem ordinary_step (limit : Nat) (state : State Symbol Guard) (coherent : Coherent state)
    (seen laterSeen : List Nat) (pending laterPending : List (Value Symbol Guard))
    (visited : ∀ identity ∈ seen, identity ∈ laterSeen) (smaller : workWeight laterPending < workWeight pending) :
    HeightOrder.VectorBelow (limit + 1) (measure limit state laterSeen laterPending) (measure limit state seen pending) := by
  apply HeightOrder.vector_decreases (limit + 1) _ _ ⟨0, by omega⟩ smaller
  intro index above
  obtain ⟨degree, inside⟩ := index
  cases degree with
  | zero => simp at above
  | succ degree =>
      change count state laterSeen degree ≤ count state seen degree
      apply count_mono state state coherent.valid.2 coherent.valid.2 seen laterSeen degree
      intro identity selected
      have facts : identity ∉ laterSeen ∧ rankAt state identity = some degree := by simpa [unseenAt] using selected
      simp only [unseenAt, decide_eq_true_eq]
      exact ⟨fun member => facts.1 (visited identity member), facts.2⟩

/-- An unseen Mu consumes its actual degree and can increase only lower-priority budget entries. -/
theorem mu_step (limit : Nat) (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (afterCoherent : Coherent after) (bounded : Bounded before limit)
    (seen : List Nat) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary)) (unseen : entry.identity ∉ seen)
    (lower : InternedStoredPlanBinderDepthProgress.Lower before (InternedStoredPlanBinderDepth.valueDepth body) after)
    (pending laterPending : List (Value Symbol Guard)) :
    HeightOrder.VectorBelow (limit + 1) (measure limit after (entry.identity :: seen) laterPending)
      (measure limit before seen pending) := by
  have inside := bounded entry.key entry body depth ordinary present
  let height : Fin (limit + 1) := ⟨InternedStoredPlanBinderDepth.valueDepth body + 1, by omega⟩
  apply HeightOrder.vector_decreases (limit + 1) _ _ height
  · exact count_after_lt before after beforeCoherent afterCoherent seen entry body depth ordinary present unseen lower
  · intro index above
    obtain ⟨degree, valid⟩ := index
    cases degree with
    | zero => simp [height] at above
    | succ degree =>
        change count after (entry.identity :: seen) degree ≤ count before seen degree
        have higher : InternedStoredPlanBinderDepth.valueDepth body < degree := by simpa [height] using above
        exact count_after_le before after beforeCoherent afterCoherent seen entry.identity _ degree lower (by omega)

/-- Every actual closed cold worklist completes with exact edges and cache, without preparation. -/
theorem collect_complete [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state)
    (bounded : Bounded state limit) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (closed : ClosedValues pending) :
    ∃ fuel edges after, collect fuel state seen pending = .done edges after ∧
      InternedOpenDepthReadback.Heap after ∧ Bounded after limit := by
  cases pending with
  | nil => exact ⟨0, [], state, rfl, heap, bounded⟩
  | cons value rest =>
      have available := inputs value List.mem_cons_self
      have valueClosed := closed value List.mem_cons_self
      have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
      have facts := semantic.1.normal.facts
      have tailDecrease := ordinary_step limit state facts.coherent seen seen (value :: rest) rest
        (fun _ member => member) (by simp only [workWeight]; have positive := weight_positive value; omega)
      cases value with
      | empty =>
          obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ :=
            collect_complete limit state semantic covered heap bounded seen rest restInputs restClosed
          exact ⟨fuel + 1, edges, after, done, afterHeap, afterBounded⟩
      | reference name => simp [Value.free] at valueClosed
      | node entry own depth free =>
          obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ :=
            collect_complete limit state semantic covered heap bounded seen rest restInputs restClosed
          exact ⟨fuel + 1, own ++ edges, after, by simp only [collect, done, MergedSourceExposure.Result.prepend], afterHeap, afterBounded⟩
      | union entry members depth free =>
          by_cases visited : entry.identity ∈ seen
          · obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ :=
              collect_complete limit state semantic covered heap bounded seen rest restInputs restClosed
            exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_left visited] using done, afterHeap, afterBounded⟩
          · have nextInputs : Values state (members ++ rest) := by
              intro child member
              rcases List.mem_append.mp member with first | later
              · exact available.children child first
              · exact restInputs child later
            have nextClosed : ClosedValues (members ++ rest) := by
              intro child member
              rcases List.mem_append.mp member with first | later
              · exact MergedColdReaderClosed.union_members_closed state facts entry members depth free available valueClosed child first
              · exact restClosed child later
            have unionDecrease := ordinary_step limit state facts.coherent seen (entry.identity :: seen)
              (.union entry members depth free :: rest) (members ++ rest) (fun _ member => List.mem_cons_of_mem _ member)
              (by simp only [workWeight, weight, workWeight_append]; omega)
            obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ := collect_complete limit state semantic covered heap bounded
              (entry.identity :: seen) (members ++ rest) nextInputs nextClosed
            exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_right visited] using done, afterHeap, afterBounded⟩
      | mu entry body depth ordinary =>
          by_cases visited : entry.identity ∈ seen
          · obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ :=
              collect_complete limit state semantic covered heap bounded seen rest restInputs restClosed
            exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_left visited] using done, afterHeap, afterBounded⟩
          · obtain ⟨result, middle, unfolded, middleContext, middleCached, middleCovered, resultAvailable, growth, history⟩ :=
              InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                state semantic.1 available semantic.2 covered
            have lower : InternedStoredPlanBinderDepthProgress.Lower state (InternedStoredPlanBinderDepth.valueDepth body) middle := by
              simpa only [unfolded, InternedNestedConstruction.Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
                InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary) state
                  semantic.1 semantic.2 heap available valueClosed
            have middleHeap : InternedOpenDepthReadback.Heap middle := by
              simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
                InternedStoredPlanBinderDepthProgress.unfold_heap (.mu entry body depth ordinary) state semantic.1 semantic.2 heap available
            have present := available.resident entry rfl
            have middleBounded := bounded_after state middle limit (InternedStoredPlanBinderDepth.valueDepth body)
              bounded (bounded entry.key entry body depth ordinary present) lower
            have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
              state semantic.1 available valueClosed result middle unfolded
            have nextInputs : Values middle (result :: rest) := by
              intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact resultAvailable
              · exact (restInputs child member).grows state middle growth history
            have nextClosed : ClosedValues (result :: rest) := by
              intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact resultClosed
              · exact restClosed child member
            have muDecrease := mu_step limit state middle facts.coherent middleContext.normal.facts.coherent bounded seen
              entry body depth ordinary present visited lower (.mu entry body depth ordinary :: rest) (result :: rest)
            obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ := collect_complete limit middle
              ⟨middleContext, middleCached⟩ middleCovered middleHeap middleBounded (entry.identity :: seen) (result :: rest) nextInputs nextClosed
            exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_right visited, unfolded] using done, afterHeap, afterBounded⟩
termination_by measure limit state seen pending
decreasing_by
  all_goals simp_wf
  all_goals simp_all only
  all_goals first | exact tailDecrease | exact unionDecrease | exact muDecrease

/-- Both actual public reader paths complete and retain the fixed Mu-depth bound. -/
theorem nodeEdges_complete_bounded [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state) (bounded : Bounded state limit)
    (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      InternedOpenDepthReadback.Heap after ∧ Bounded after limit := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (currentHeap : InternedOpenDepthReadback.Heap current)
      (currentBounded : Bounded current limit) (rootAvailable : Available current root) (rootClosed : root.free = []) :
      ∃ fuel edges after, (collect fuel current [] [root]).canonical = .done edges after ∧
        InternedOpenDepthReadback.Heap after ∧ Bounded after limit := by
    obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ := collect_complete limit current currentSemantic currentCovered
      currentHeap currentBounded [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed)
    exact ⟨fuel, canonicalEdges edges, after, by rw [done]; rfl, afterHeap, afterBounded⟩
  cases value with
  | empty | reference => exact ⟨0, [], state, rfl, heap, bounded⟩
  | node entry edges depth free => exact ⟨0, edges, state, rfl, heap, bounded⟩
  | union entry members depth free => exact fallback _ state semantic covered heap bounded available closed
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, middleContext, middleCached, middleCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have middleHeap : InternedOpenDepthReadback.Heap middle := by
        simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
          InternedStoredPlanBinderDepthProgress.unfold_heap (.mu entry body depth ordinary) state semantic.1 semantic.2 heap available
      have lower : InternedStoredPlanBinderDepthProgress.Lower state (InternedStoredPlanBinderDepth.valueDepth body) middle := by
        simpa only [unfolded, InternedNestedConstruction.Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
          InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary) state semantic.1 semantic.2 heap available closed
      have middleBounded := bounded_after state middle limit (InternedStoredPlanBinderDepth.valueDepth body) bounded
        (bounded entry.key entry body depth ordinary (available.resident entry rfl)) lower
      have rootAvailable := available.grows state middle growth history
      obtain ⟨fuel, edges, after, done, afterHeap, afterBounded⟩ := fallback (.mu entry body depth ordinary) middle
        ⟨middleContext, middleCached⟩ middleCovered middleHeap middleBounded rootAvailable closed
      cases result with
      | node entry edges depth free => exact ⟨0, edges, middle, by simp only [nodeEdges, unfolded], middleHeap, middleBounded⟩
      | empty | reference | union | mu =>
          exact ⟨fuel, edges, after, by simpa only [nodeEdges, unfolded] using done, afterHeap, afterBounded⟩

/-- The actual finite issued inventory supplies every numeric premise of public reader completion. -/
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧ InternedOpenDepthReadback.Heap after := by
  obtain ⟨fuel, edges, after, done, afterHeap, _⟩ := nodeEdges_complete_bounded
    (maximumDepth (nodeInventory state) + 1) value state semantic covered heap
    (initial_bounded state semantic.1.normal.facts) available closed
  exact ⟨fuel, edges, after, done, afterHeap⟩

/-- General closed repaired reads have exact successful effects and stable values and caches at every larger bound. -/
theorem read_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      SemanticHeap after ∧ Covered [] after ∧ InternedOpenDepthReadback.Heap after ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      InternedNestedProvenance.Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, nodeEdges (fuel + extra) value state = .done edges after := by
  obtain ⟨fuel, edges, after, done, afterHeap⟩ := nodeEdges_complete value state semantic covered heap available closed
  have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value state semantic covered available closed
  refine ⟨fuel, edges, after, done, ?_, ?_, afterHeap, ?_, ?_, checked.edges edges after done, checked.closed edges after done, ?_⟩
  · simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
  · simpa only [done, MergedSourceExposure.Result.state] using checked.covered
  · simpa only [done, MergedSourceExposure.Result.state] using checked.growth
  · simpa only [done, MergedSourceExposure.Result.state] using checked.history
  · intro extra
    exact (MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra value state
      (by simp only [done, MergedSourceExposure.Finished])).trans done

/-- Actual closed source construction derives every heap premise of a finite stable repaired cold read. -/
theorem constructed_read_closed [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      SemanticHeap after ∧ Covered [] after ∧ InternedOpenDepthReadback.Heap after ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      InternedNestedProvenance.Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, nodeEdges (fuel + extra) value state = .done edges after := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value state built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression value state built
  have heap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  exact read_closed value state semantic covered heap available closed

end MicroCFTA.MergedFreshOrdinaryColdTermination
