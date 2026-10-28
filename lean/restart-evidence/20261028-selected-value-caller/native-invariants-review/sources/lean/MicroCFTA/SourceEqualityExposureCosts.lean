import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.SourceEqualityAnnotationExposure
import MicroCFTA.InternedFreshOrdinaryStoredCosts

/-!
# Semantic and weighted heaps through actual bounded row exposure

Each actual unfold retains both heap invariants and available operands.
The bounded worklist retains them at every outcome, including unresolved
and exhausted reads. Complete row reads return resident edges. These
effects do not assert language completeness or traversal termination.
-/
namespace MicroCFTA.SourceEqualityExposureCosts
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open MergedSourceExposure (Result)
open MergedFreshOrdinaryExposure
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationExposure (prepend_state canonical_state)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Semantic readiness and weighted records supply the complete older gate invariant. -/
theorem gate_ready {state : State Symbol Guard} (semantic : SemanticReady state) (costs : CostHeap state) :
    InternedFreshOrdinaryMemoGateTrace.Ready state :=
  ⟨semantic.ready.semantic.1, semantic.ready.semantic.2, semantic.ready.covered, costs⟩

/-- Every actual reader outcome retains semantic heaps, weighted records, and resident completed rows. -/
structure Verified (before : State Symbol Guard) (result : Result Symbol Guard) : Prop where
  semantic : SemanticReady result.state
  costs : CostHeap result.state
  keeps : Keeps before result.state
  rows : ∀ edges after, result = .done edges after → Edges after edges

private theorem done_verified (state : State Symbol Guard) (semantic : SemanticReady state)
    (costs : CostHeap state) (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges) :
    Verified state (.done edges state) :=
  ⟨semantic, costs, pure_keeps state semantic.ready, by intro _ _ same; cases same; exact resident⟩

private theorem Verified.extend {before middle : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified middle result) (keeps : Keeps before middle) : Verified before result :=
  ⟨verified.semantic, verified.costs, keeps.trans verified.keeps, verified.rows⟩

private theorem Verified.prepend {before : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified before result) (edges : List (EdgeValue Symbol Guard)) (resident : Edges before edges) :
    Verified before (result.prepend edges) := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.semantic, verified.costs, verified.keeps, ?_⟩
      intro output final same
      cases same
      intro edge member
      rcases List.mem_append.mp member with first | later
      · exact InternedEdgeResidency.edge_grows before after verified.keeps.growth edge (resident edge first)
      · exact verified.rows values after rfl edge later

private theorem Verified.canonical {before : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified before result) : Verified before result.canonical := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.semantic, verified.costs, verified.keeps, ?_⟩
      intro output final same
      cases same
      exact fun edge member => verified.rows values after rfl edge (canonicalEdges_member values edge member)

/-- Every bounded actual worklist retains cost and semantic heaps without a closed-input premise. -/
theorem collect_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (semantic : SemanticReady state) (costs : CostHeap state) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    Verified state (collect fuel state seen pending) := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => exact done_verified state semantic costs [] (by simp [Edges])
      | cons => exact ⟨semantic, costs, pure_keeps state semantic.ready, by intro _ _ impossible; cases impossible⟩
  | succ fuel ih =>
      cases pending with
      | nil => exact done_verified state semantic costs [] (by simp [Edges])
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic costs seen rest restInputs
          | reference => exact ⟨semantic, costs, pure_keeps state semantic.ready, by intro _ _ impossible; cases impossible⟩
          | node entry edges depth free =>
              exact (ih state semantic costs seen rest restInputs).prepend edges
                (InternedEdgeResidency.resident_edges state semantic.ready.semantic.1.normal.facts.linked _ available.resident)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic costs seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic costs (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic costs seen rest restInputs
              · obtain ⟨result, after, done, kept, finalSemantic, resultAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have retained := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap (.mu entry body depth ordinary)
                  state semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
                have finalCosts : CostHeap after := by simpa only [done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  (ih after finalSemantic finalCosts (entry.identity :: seen) (result :: rest) nextInputs).extend kept

/-- Both actual row-reader branches retain cost and semantic heaps at every bounded outcome. -/
theorem nodeEdges_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticReady state) (costs : CostHeap state)
    (available : Available state value) : Verified state (nodeEdges fuel value state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current) (currentCosts : CostHeap current)
      (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Verified current (collect fuel current [] [root]).canonical :=
    (collect_verified fuel current currentSemantic currentCosts [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)).canonical
  cases value with
  | empty | reference => exact done_verified state semantic costs [] (by simp [Edges])
  | node entry edges depth free =>
      exact done_verified state semantic costs edges
        (InternedEdgeResidency.resident_edges state semantic.ready.semantic.1.normal.facts.linked _ available.resident)
  | union => exact fallback state semantic costs _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, finalSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap (.mu entry body depth ordinary)
        state semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have finalCosts : CostHeap after := by simpa only [done, Outcome.state] using retained
      have following := (fallback after finalSemantic finalCosts (.mu entry body depth ordinary)
        (kept.available _ available)).extend kept
      cases result with
      | node own edges level free =>
          simpa only [nodeEdges, done] using
            (done_verified after finalSemantic finalCosts edges
              (InternedEdgeResidency.resident_edges after finalSemantic.ready.semantic.1.normal.facts.linked _ resultAvailable.resident)).extend kept
      | empty | reference | union | mu => simpa only [nodeEdges, done] using following

end MicroCFTA.SourceEqualityExposureCosts
