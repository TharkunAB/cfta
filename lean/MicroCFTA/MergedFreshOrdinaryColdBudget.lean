import MicroCFTA.InternedFreshMuUnfoldBudget

/-!
# Exact cache progress through repaired cold reads

Every completed closed read retains the body/probe heap and the fixed
maximum degree. It either reduces the unfinished-unfolding vector or
returns the identical cache. No fixed future inventory is required.
-/
namespace MicroCFTA.MergedFreshOrdinaryColdBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedMuDepthInventory (Bounded bounded_after)
open InternedFreshMuUnfoldBudget (Progress)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)

noncomputable section

/-- Every completed actual closed collector retains the heap and makes exact global cache progress. -/
theorem collect_progress [DecidableEq (EdgeKey Symbol Guard)] (fuel limit : Nat)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : InternedOpenDepthReadback.Heap before) (bounded : Bounded before limit)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values before pending) (closed : ClosedValues pending)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel before seen pending = .done edges after) :
    InternedOpenDepthReadback.Heap after ∧ Bounded after limit ∧ Progress limit before after := by
  induction fuel generalizing before seen pending edges after with
  | zero =>
      cases pending with
      | nil => cases done; exact ⟨heap, bounded, Or.inr rfl⟩
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; exact ⟨heap, bounded, Or.inr rfl⟩
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have tailInputs : Values before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have tailClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih before semantic covered heap bounded seen rest tailInputs tailClosed edges after done
          | reference name => simp [Value.free] at valueClosed
          | node entry own depth free =>
              cases tail : collect fuel before seen rest with
              | unresolved | pending | exhausted => simp only [collect, tail, Result.prepend] at done; cases done
              | done rows final =>
                  have equal : own ++ rows = edges ∧ final = after := by
                    simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
                  obtain ⟨_, rfl⟩ := equal
                  exact ih before semantic covered heap bounded seen rest tailInputs tailClosed rows final tail
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · exact ih before semantic covered heap bounded seen rest tailInputs tailClosed edges after
                  (by simpa only [collect, ite_eq_left visited] using done)
              · have nextInputs : Values before (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact tailInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact MergedColdReaderClosed.union_members_closed before semantic.1.normal.facts
                      entry members depth free available valueClosed child first
                  · exact tailClosed child later
                exact ih before semantic covered heap bounded (entry.identity :: seen) (members ++ rest) nextInputs nextClosed edges after
                  (by simpa only [collect, ite_eq_right visited] using done)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · exact ih before semantic covered heap bounded seen rest tailInputs tailClosed edges after
                  (by simpa only [collect, ite_eq_left visited] using done)
              · obtain ⟨result, middle, unfolded, middleContext, middleCached, middleCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    before semantic.1 available semantic.2 covered
                have middleHeap : InternedOpenDepthReadback.Heap middle := by
                  simpa only [unfolded, Outcome.state] using InternedStoredPlanBinderDepthProgress.unfold_heap
                    (.mu entry body depth ordinary) before semantic.1 semantic.2 heap available
                have lower : InternedStoredPlanBinderDepthProgress.Lower before (InternedStoredPlanBinderDepth.valueDepth body) middle := by
                  simpa only [unfolded, Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
                    InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary)
                      before semantic.1 semantic.2 heap available valueClosed
                have middleBounded := bounded_after before middle limit _ bounded
                  (bounded entry.key entry body depth ordinary (available.resident entry rfl)) lower
                have firstProgress := InternedFreshMuUnfoldBudget.unfold_progress limit (.mu entry body depth ordinary)
                  before semantic covered heap bounded available valueClosed result middle unfolded
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  before semantic.1 available valueClosed result middle unfolded
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact resultAvailable
                  · exact (tailInputs child later).grows before middle growth history
                have nextClosed : ClosedValues (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact resultClosed
                  · exact tailClosed child later
                have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                obtain ⟨afterHeap, afterBounded, laterProgress⟩ := ih middle ⟨middleContext, middleCached⟩ middleCovered
                  middleHeap middleBounded (entry.identity :: seen) (result :: rest) nextInputs nextClosed edges after tail
                exact ⟨afterHeap, afterBounded, Progress.trans limit before middle after firstProgress laterProgress⟩

/-- Canonical edge order preserves the exact global cache-progress result. -/
theorem canonical_progress [DecidableEq (EdgeKey Symbol Guard)] (fuel limit : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : InternedOpenDepthReadback.Heap before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = []) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : (collect fuel before [] [value]).canonical = .done edges after) :
    InternedOpenDepthReadback.Heap after ∧ Bounded after limit ∧ Progress limit before after := by
  cases read : collect fuel before [] [value] with
  | unresolved | pending | exhausted => simp only [read, Result.canonical] at done; cases done
  | done rows final =>
      have equal : canonicalEdges rows = edges ∧ final = after := by
        simpa only [read, Result.canonical, Result.done.injEq] using done
      obtain ⟨_, rfl⟩ := equal
      exact collect_progress fuel limit before semantic covered heap bounded [] [value]
        (by intro child member; simpa only [List.mem_singleton.mp member] using available)
        (by intro child member; simpa only [List.mem_singleton.mp member] using closed) rows final read

/-- Both actual public reader paths retain the heap and either consume the budget or keep the exact cache. -/
theorem nodeEdges_progress [DecidableEq (EdgeKey Symbol Guard)] (fuel limit : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : InternedOpenDepthReadback.Heap before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = []) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : nodeEdges fuel value before = .done edges after) :
    InternedOpenDepthReadback.Heap after ∧ Bounded after limit ∧ Progress limit before after := by
  cases value with
  | empty | reference | node => cases done; exact ⟨heap, bounded, Or.inr rfl⟩
  | union entry members depth free => exact canonical_progress fuel limit _ before semantic covered heap bounded available closed edges after done
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, middleContext, middleCached, middleCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          before semantic.1 available semantic.2 covered
      have middleHeap : InternedOpenDepthReadback.Heap middle := by
        simpa only [unfolded, Outcome.state] using InternedStoredPlanBinderDepthProgress.unfold_heap
          (.mu entry body depth ordinary) before semantic.1 semantic.2 heap available
      have lower : InternedStoredPlanBinderDepthProgress.Lower before (InternedStoredPlanBinderDepth.valueDepth body) middle := by
        simpa only [unfolded, Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
          InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary)
            before semantic.1 semantic.2 heap available closed
      have middleBounded := bounded_after before middle limit _ bounded
        (bounded entry.key entry body depth ordinary (available.resident entry rfl)) lower
      have firstProgress := InternedFreshMuUnfoldBudget.unfold_progress limit (.mu entry body depth ordinary)
        before semantic covered heap bounded available closed result middle unfolded
      have rootAvailable := available.grows before middle growth history
      cases result with
      | node actual own depth free =>
          have equal : own = edges ∧ middle = after := by simpa only [nodeEdges, unfolded, Result.done.injEq] using done
          obtain ⟨_, rfl⟩ := equal
          exact ⟨middleHeap, middleBounded, firstProgress⟩
      | empty | reference | union | mu =>
          have tail : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges after := by
            simpa only [nodeEdges, unfolded] using done
          obtain ⟨afterHeap, afterBounded, laterProgress⟩ := canonical_progress fuel limit _ middle
            ⟨middleContext, middleCached⟩ middleCovered middleHeap middleBounded rootAvailable closed edges after tail
          exact ⟨afterHeap, afterBounded, Progress.trans limit before middle after firstProgress laterProgress⟩

end
end MicroCFTA.MergedFreshOrdinaryColdBudget
