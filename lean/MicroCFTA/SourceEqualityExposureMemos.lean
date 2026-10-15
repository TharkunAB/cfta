import MicroCFTA.SourceQueryUnfoldMemo
import MicroCFTA.SourceEqualityExposureCosts

/-!
# Actual global unfolding calls during bounded row exposure

The receipt graph follows each demanded worklist item. Mu reads retain
the actual global memo call and constructor readback. Visited values do
not call the memo. A nonordinary first Mu result restarts collection on
the original value in the returned heap and memo. All bounded outcomes
retain coherent saved entries. This is not a GHC publication proof.
-/
namespace MicroCFTA.SourceEqualityExposureMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedFreshOrdinaryExposure
open SourceEqualityAnnotationExposure (prepend_state canonical_state)
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo
local notation "Correct" => InternedFreshOrdinaryUnfoldMemo.Correct
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A bounded collection records exactly its visited Mu memo calls in source order. -/
inductive CollectReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → State Symbol Guard → List Nat → List (Value Symbol Guard) →
      UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | nil : CollectReads fuel state seen [] memo memo
  | zero : CollectReads 0 state seen (value :: rest) memo memo
  | empty (tail : CollectReads fuel state seen rest memo saved) :
      CollectReads (fuel + 1) state seen (.empty :: rest) memo saved
  | reference : CollectReads (fuel + 1) state seen (.reference name :: rest) memo memo
  | node (tail : CollectReads fuel state seen rest memo saved) :
      CollectReads (fuel + 1) state seen (.node entry edges depth free :: rest) memo saved
  | union_seen (visited : entry.identity ∈ seen) (tail : CollectReads fuel state seen rest memo saved) :
      CollectReads (fuel + 1) state seen (.union entry members depth free :: rest) memo saved
  | union_more (fresh : entry.identity ∉ seen)
      (tail : CollectReads fuel state (entry.identity :: seen) (members ++ rest) memo saved) :
      CollectReads (fuel + 1) state seen (.union entry members depth free :: rest) memo saved
  | mu_seen (visited : entry.identity ∈ seen) (tail : CollectReads fuel state seen rest memo saved) :
      CollectReads (fuel + 1) state seen (.mu entry body depth ordinary :: rest) memo saved
  | mu_unfold (fresh : entry.identity ∉ seen)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (called : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memo state = .done (next, middleMemo) after)
      (tail : CollectReads fuel after (entry.identity :: seen) (next :: rest) middleMemo saved) :
      CollectReads (fuel + 1) state seen (.mu entry body depth ordinary :: rest) memo saved

/-- A physical row read retains its first Mu call and its exact optional fallback. -/
inductive NodeEdgesReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Value Symbol Guard → State Symbol Guard → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | empty : NodeEdgesReads fuel .empty state memo memo
  | reference : NodeEdgesReads fuel (.reference name) state memo memo
  | node : NodeEdgesReads fuel (.node entry edges depth free) state memo memo
  | union (read : CollectReads fuel state [] [.union entry members depth free] memo saved) :
      NodeEdgesReads fuel (.union entry members depth free) state memo saved
  | mu
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (called : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memo state = .done (next, middleMemo) after)
      (rest : match next with
        | .node .. => saved = middleMemo
        | _ => CollectReads fuel after [] [.mu entry body depth ordinary] middleMemo saved) :
      NodeEdgesReads fuel (.mu entry body depth ordinary) state memo saved

/-- Every actual bounded collection derives coherent memo calls and retains earlier saved entries. -/
theorem collect_reads [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state) (costs : CostHeap state)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending)
    (memo : UMemo Symbol Guard) (correct : Correct state memo) :
    ∃ saved, CollectReads fuel state seen pending memo saved ∧
      Correct (collect fuel state seen pending).state saved ∧ Extends memo saved := by
  induction fuel generalizing state seen pending memo with
  | zero =>
      cases pending with
      | nil => exact ⟨memo, .nil, correct, extends_refl _⟩
      | cons => exact ⟨memo, .zero, correct, extends_refl _⟩
  | succ fuel ih =>
      cases pending with
      | nil => exact ⟨memo, .nil, correct, extends_refl _⟩
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty =>
              obtain ⟨saved, tail, valid, retained⟩ := ih state semantic costs seen rest restInputs memo correct
              exact ⟨saved, .empty tail, valid, retained⟩
          | reference => exact ⟨memo, .reference, correct, extends_refl _⟩
          | node entry edges depth free =>
              obtain ⟨saved, tail, valid, retained⟩ := ih state semantic costs seen rest restInputs memo correct
              exact ⟨saved, .node tail, by simpa only [collect, prepend_state] using valid, retained⟩
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · obtain ⟨saved, tail, valid, retained⟩ := ih state semantic costs seen rest restInputs memo correct
                exact ⟨saved, .union_seen visited tail,
                  by simpa only [collect, ite_eq_left visited] using valid, retained⟩
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                obtain ⟨saved, tail, valid, retained⟩ :=
                  ih state semantic costs (entry.identity :: seen) (members ++ rest) nextInputs memo correct
                exact ⟨saved, .union_more visited tail,
                  by simpa only [collect, ite_eq_right visited] using valid, retained⟩
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · obtain ⟨saved, tail, valid, retained⟩ := ih state semantic costs seen rest restInputs memo correct
                exact ⟨saved, .mu_seen visited tail,
                  by simpa only [collect, ite_eq_left visited] using valid, retained⟩
              · obtain ⟨next, after, actual, kept, finalSemantic, nextAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have weighted := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap (.mu entry body depth ordinary)
                  state semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
                have finalCosts : CostHeap after := by simpa only [actual, Outcome.state] using weighted
                obtain ⟨middleMemo, called, middleCorrect, retained, _, _⟩ :=
                  SourceQueryUnfoldMemo.run_of_unfold (.mu entry body depth ordinary) next state after
                    actual semantic costs available memo correct
                have nextInputs : Values after (next :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact nextAvailable
                  · exact kept.available child (restInputs child member)
                obtain ⟨saved, tail, valid, later⟩ :=
                  ih after finalSemantic finalCosts (entry.identity :: seen) (next :: rest) nextInputs middleMemo middleCorrect
                exact ⟨saved, .mu_unfold visited actual called tail,
                  by simpa only [collect, ite_eq_right visited, actual] using valid, extends_trans retained later⟩

/-- Every actual bounded row reader derives its exact global unfolding calls and retained coherent entries. -/
theorem nodeEdges_reads [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (costs : CostHeap state) (available : Available state value)
    (memo : UMemo Symbol Guard) (correct : Correct state memo) :
    ∃ saved, NodeEdgesReads fuel value state memo saved ∧
      Correct (nodeEdges fuel value state).state saved ∧ Extends memo saved := by
  cases value with
  | empty => exact ⟨memo, .empty, correct, extends_refl _⟩
  | reference => exact ⟨memo, .reference, correct, extends_refl _⟩
  | node => exact ⟨memo, .node, correct, extends_refl _⟩
  | union entry members depth free =>
      obtain ⟨saved, read, valid, retained⟩ := collect_reads fuel state semantic costs []
        [.union entry members depth free] (by intro child member; simpa only [List.mem_singleton.mp member] using available) memo correct
      exact ⟨saved, .union read, by simpa only [nodeEdges, canonical_state] using valid, retained⟩
  | mu entry body depth ordinary =>
      obtain ⟨next, after, actual, kept, finalSemantic, nextAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have weighted := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap (.mu entry body depth ordinary)
        state semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have finalCosts : CostHeap after := by simpa only [actual, Outcome.state] using weighted
      obtain ⟨middleMemo, called, middleCorrect, retained, _, _⟩ :=
        SourceQueryUnfoldMemo.run_of_unfold (.mu entry body depth ordinary) next state after
          actual semantic costs available memo correct
      have fallback := collect_reads fuel after finalSemantic finalCosts [] [.mu entry body depth ordinary]
        (by intro child member; simpa only [List.mem_singleton.mp member] using kept.available _ available) middleMemo middleCorrect
      cases next with
      | node => exact ⟨middleMemo, .mu actual called rfl,
          by simpa only [nodeEdges, actual, MergedSourceExposure.Result.state] using middleCorrect, retained⟩
      | empty | reference | union | mu =>
          obtain ⟨saved, read, valid, later⟩ := fallback
          exact ⟨saved, .mu actual called read,
            by simpa only [nodeEdges, actual, canonical_state] using valid, extends_trans retained later⟩

end MicroCFTA.SourceEqualityExposureMemos
