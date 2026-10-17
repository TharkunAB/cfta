import MicroCFTA.SourceCurrentConstrainedCapGuardNative
import MicroCFTA.SourceCurrentMergedHeapEffects

/-!
# Causal guard heaps through actual merge comparisons

Actual recursive row exposure uses the repaired stored executor. Its produced
Mu guard heap passes through every completed comparison and selection.
Operands can contain unrelated constrained guards and open references.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMergeGuardEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityRequiredSemanticCache
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)


private theorem unfold_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticReady state)
    (available : Available state value) (heap : Heap property state) :
    Heap property (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      apply SourceCurrentConstrainedCapGuardNative.execute_heap property body _ state semantic.ready.semantic
        (available.children body (by simp [InternedProbeProvenance.children])) _ heap
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · cases found

/-- Bounded collection retains causal guard observations with unrelated open inputs. -/
private theorem collect_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state)
    (heap : Heap property state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Heap property (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state semantic heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have retained := unfold_heap property (.mu entry body depth ordinary) state semantic available heap
                have afterHeap : Heap property after := by
                  simpa only [done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  ih after afterSemantic afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Actual direct and closure reads retain causal guard observations without whole-value closedness. -/
private theorem nodeEdges_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (heap : Heap property state) (available : Available state value) :
    Heap property (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current)
      (currentHeap : Heap property current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap property (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap property fuel current currentSemantic currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic heap _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := unfold_heap property (.mu entry body depth ordinary) state semantic available heap
      have afterHeap : Heap property after := by
        simpa only [done, Outcome.state] using retained
      have closure := fallback after afterSemantic afterHeap (.mu entry body depth ordinary)
        (kept.available _ available)
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure


open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done)
open SourceCurrentConstrainedCapGuardHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A successful stage retains actual cache effects and preserves causal guard observations. -/
structure Effect (annotation : Guard → Prop) (before after : State Symbol Guard) : Prop where
  /-- Actual complete records and issued identities remain available. -/
  keeps : Keeps before after
  /-- The returned heap retains its semantic readiness. -/
  semantic : SemanticReady after
  /-- The returned heap retains stored unfolding costs. -/
  costs : CostHeap after
  /-- The produced guard heap follows the same actual effects. -/
  guards : Heap annotation before → Heap annotation after

/-- Guard effects retain the previously proved source cache effects. -/
theorem Effect.original {annotation : Guard → Prop} {before after : State Symbol Guard} (effect : Effect annotation before after) :
    SourceMergedComparisonEffects.Effect before after := ⟨effect.keeps, effect.semantic⟩

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (annotation : Guard → Prop) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect annotation before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩

/-- Ordered successful effects compose semantic caches, histories, and guard preservation. -/
theorem Effect.trans {annotation : Guard → Prop} {before middle after : State Symbol Guard} (first : Effect annotation before middle) (second : Effect annotation middle after) : Effect annotation before after :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, fun heap => second.guards (first.guards heap)⟩

/-- A completed actual row read retains both heaps and returns resident rows. -/
theorem read_effect (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Effect annotation before after ∧ Edges after rows := by
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done edges final =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have kept : Keeps before after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.keeps
      have ready : SemanticReady after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.semantic
      have retained : CostHeap after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.costs
      refine ⟨⟨kept, ready, retained, ?_⟩, checked.rows rows after actual⟩
      intro heap
      simpa only [actual, MergedSourceExposure.Result.state] using
        nodeEdges_heap annotation fuel value before semantic heap available
  | pending | unresolved | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      cases done

/-- Callback effects use only actual available operands and their current heaps. -/
private def Callback (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    ∀ answer after, compare wide narrow before = .done answer after → Effect annotation before after

/-- The source zip conjunction preserves guard observations even when a list ends early. -/
private theorem children_effect (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback annotation compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect annotation before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect annotation before semantic costs true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect annotation before semantic costs true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic costs (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect annotation middle effect.semantic effect.costs false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic effect.costs
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member))) later)

/-- Actual ordered edge-cover search retains semantic cache fields and causal guard observations. -/
private theorem anyCover_effect (annotation : Guard → Prop) [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic costs false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect annotation compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect annotation middle effect.semantic effect.costs true answer after later)
        | false => exact effect.trans (ih middle effect.semantic effect.costs (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge (wideInputs edge (List.mem_cons_of_mem _ member))) later)
      · exact ih before semantic costs narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member)) done

/-- Each actual row read and cover search retains guard observations and the next input scope. -/
private theorem allRows_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect annotation before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect annotation before semantic costs true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := read_effect annotation fuel wide before semantic costs wideInput wides readAfter read
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect annotation clear compare callback narrow wides readAfter readFacts.1.semantic readFacts.1.costs
        (fun value member => readFacts.1.keeps.available value (childInputs value member)) readFacts.2 accepted middle covered
      have first : Effect annotation before middle := readFacts.1.trans coverFacts
      cases accepted with
      | false => exact first.trans (pure_effect annotation middle first.semantic first.costs false answer after rest)
      | true => exact first.trans (ih middle first.semantic first.costs (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member))) rest)

/-- Every completed structural comparison retains costs and guard observations on available open or closed operands. -/
theorem check_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect annotation before after := by
  rw [check] at done
  split at done
  · exact pure_effect annotation before semantic costs true answer after done
  · split at done
    · exact pure_effect annotation before semantic costs false answer after done
    · split at done
      · exact pure_effect annotation before semantic costs true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect annotation before semantic costs true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := read_effect annotation (fuel + 1) narrow before semantic costs narrowInput narrows middle read
                      have rest := allRows_effect annotation (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect annotation clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.1.semantic readFacts.1.costs
                        (readFacts.1.keeps.available wide wideInput) readFacts.2 answer after later
                      exact readFacts.1.trans rest
termination_by fuel


open MergedPhysicalGroupColumns (closedMu)

/-- Every completed recursive-cover scan retains guard observations and actual cache histories. -/
theorem anyAccepts_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (answer : Bool) (after : State Symbol Guard) (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic costs false answer after done
  | cons wide wides ih =>
      by_cases narrowClosed : narrow.free = []
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done
        obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effects := check_effect annotation clear fuel [] wide narrow before semantic costs (wideInputs _ List.mem_cons_self) narrowInput accepted middle first
        cases accepted with
        | true => exact effects.trans (pure_effect annotation middle effects.semantic effects.costs true answer after later)
        | false => exact effects.trans (ih middle effects.semantic effects.costs (effects.keeps.available narrow narrowInput)
            (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member))) later)
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_false] at done
        exact pure_effect annotation before semantic costs false answer after done

/-- Successful actual filtering retains guard heaps, semantic heaps, and both histories. -/
theorem retain_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) : Effect annotation before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩
  | cons child inputs ih =>
      rw [SourceMergedSelection.retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.2
        exact ih before semantic costs recInputs (fun value member => available value (List.mem_cons_of_mem _ member)) rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := anyAccepts_effect annotation clear fuel child recursive before semantic costs (available _ List.mem_cons_self) recInputs covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.semantic effects.costs (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member))) rest after tail)

/-- The actual retention and identity filter preserve guard observations at the returned cache. -/
theorem select_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done retained after) : Effect annotation before after := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  have checked := retain_effect annotation clear fuel (inputs.filter closedMu) inputs before semantic costs
    (fun value member => available value (List.mem_filter.mp member).1) available values middle filtered
  have parts := Result.done.inj returned
  cases parts.2
  exact checked


end MicroCFTA.SourceCurrentConstrainedCapMergeGuardEffects
