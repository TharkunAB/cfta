import MicroCFTA.SourceCurrentOpenRowReadResources
import MicroCFTA.InternedFreshOrdinaryStoredCosts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.OpenReadKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentOpenRowReadResources
open SourceSecondaryGateHead (WarmHead)

private def expression : Syntax Nat Bool :=
  .binder false (.binder false (.node [.mk 0 false [.var 0, .var 1], .mk 1 true []]))
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def inner : Value Nat Bool := match original with | .mu _ body _ _ => body | _ => .empty
private def unfolded := InternedFreshOrdinaryStoredSubstitution.unfold inner source
private def exposed : Value Nat Bool := match unfolded with | .done value _ => value | .pending .. => .empty
private def heap := unfolded.state
private def scalar := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)

private theorem constructed : built = .done original source := by cbv
private theorem source_semantic : SemanticReady source :=
  SourceEqualityRequiredSemanticCache.constructed expression original source constructed
private theorem source_available : Available source original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original source constructed
private theorem inner_member : inner ∈ children original := by cbv; exact .head _
private theorem inner_available : Available source inner := source_available.children inner inner_member
private theorem actual : unfolded = .done exposed heap := by cbv
private theorem inner_shape : ∃ entry body depth ordinary, inner = Value.mu entry body depth ordinary := by
  have shape : (match inner with | .mu .. => True | _ => False) := by cbv
  cases found : inner with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [found] at shape
private theorem exposed_shape : ∃ entry rows depth free, exposed = Value.node entry rows depth free := by
  have shape : (match exposed with | .node .. => True | _ => False) := by cbv
  cases found : exposed with
  | node entry rows depth free => exact ⟨entry, rows, depth, free, rfl⟩
  | empty | reference | mu | union => simp only [found] at shape
private theorem inner_open : inner.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem exposed_open : exposed.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem after_properties :
    SourceEqualityRequiredCache.Keeps source heap ∧ SemanticReady heap ∧ Available heap exposed := by
  obtain ⟨value, after, done, keeps, semantic, available, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete inner source source_semantic inner_available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
  subst value
  subst after
  exact ⟨keeps, semantic, available⟩
private theorem warm_actual : InternedFreshOrdinaryStoredSubstitution.unfold inner heap = .done exposed heap :=
  InternedFreshOrdinaryStoredSubstitution.unfold_replay inner source heap exposed heap
    source_semantic.ready.semantic.1.normal.facts.coherent.valid actual (grows_refl _)
private theorem warm_support : WarmHead heap inner := by
  obtain ⟨entry, body, depth, ordinary, shape⟩ := inner_shape
  obtain ⟨own, rows, level, free, nextShape⟩ := exposed_shape
  have done := warm_actual
  rw [shape] at done
  rw [shape]
  refine .unfold done ?_
  rw [nextShape]
  exact .ordinary
private theorem available : Available heap inner :=
  inner_available.grows source heap after_properties.1.growth after_properties.1.history
private theorem initial_fits : Fits scalar heap :=
  SourceCurrentMemoMergeResourceControl.initial heap _
    (InternedValueMassHeap.initial heap after_properties.2.1.ready.semantic.1.normal.facts)
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  have sourceCosts : InternedFreshOrdinaryCostHeap.Heap source := by
    exact InternedFreshOrdinaryCosts.closed_heap expression
  have retained := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap inner source
    source_semantic.ready.semantic.1 source_semantic.ready.semantic.2 sourceCosts inner_available
  exact retained

/-- Actual nested source writes produce an open warm Mu and its own initial numeric read and Head. -/
theorem constructed_open_mu :
    ∃ (value : Value Nat Bool) (before : State Nat Bool) (q : Nat)
      (rows : List (EdgeValue Nat Bool)) (middle : State Nat Bool)
      (result : Value Nat Bool) (after : State Nat Bool),
      value.free ≠ [] ∧ WarmHead before value ∧
      MergedFreshOrdinaryExposure.collect (readFuel q) before [] [value] = .done rows middle ∧
      Fits (readGrowth q) middle ∧ rows.length ≤ readWidth q ∧
      (∃ actual : SourceEqualityRequiredHead.Head value before result after,
        Fits (headGrowth q) after ∧ Available after result ∧ SourceEqualityRequiredCache.Ordinary result ∧
        SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headGrowth q)) actual) := by
  obtain ⟨rows, middle, collected, fits, width⟩ :=
    collect_complete warm_support scalar after_properties.2.1 available initial_fits []
  obtain ⟨readRows, readAfter, done, _actual, _keeps, semantic, _readFits, _length, resident, _stable⟩ :=
    complete inner heap scalar after_properties.2.1 available warm_support initial_fits
  let result := run (makeNode readRows) readAfter
  have head : SourceEqualityRequiredHead.Head inner heap result.1 result.2 :=
    .read (readFuel scalar) readRows readAfter done rfl
  have returned := SourceCurrentOpenRowReadResources.head head scalar after_properties.2.1 costs available warm_support initial_fits
  exact ⟨inner, heap, scalar, rows, middle, result.1, result.2, inner_open, warm_support,
    collected, fits, width, head, returned.2.1, returned.2.2.1, returned.2.2.2.1, returned.2.2.2.2⟩

/-- The same produced open Mu has an exact visited skip and a stable numeric Read certificate. -/
theorem produced_visited_and_replay :
    ∃ (value : Value Nat Bool) (before : State Nat Bool) (q identity : Nat)
      (rows : List (EdgeValue Nat Bool)) (after : State Nat Bool),
      value.free ≠ [] ∧
      MergedFreshOrdinaryExposure.collect (readFuel q) before [identity] [value] = .done [] before ∧
      (∃ actual : SourceEqualityProjectionRead.Read value before rows after,
        SourceCurrentProjectionNumericReplay.ReadReady (readFuel (headGrowth q)) actual ∧
        ∀ extra, MergedFreshOrdinaryExposure.nodeEdges (readFuel q + extra) value before = .done rows after) := by
  obtain ⟨entry, body, depth, ordinary, shape⟩ := inner_shape
  obtain ⟨rows, after, done, checked, _, _, _, _, _, stable⟩ :=
    complete inner heap scalar after_properties.2.1 available warm_support initial_fits
  have fuelPositive : 0 < readFuel scalar := by unfold readFuel; omega
  have skipped : MergedFreshOrdinaryExposure.collect (readFuel scalar) heap [entry.identity] [inner] = .done [] heap := by
    rw [shape]
    obtain ⟨fuel, equal⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fuelPositive)
    rw [equal]
    simp only [MergedFreshOrdinaryExposure.collect,
      ite_eq_left (show entry.identity ∈ [entry.identity] from List.mem_cons_self)]
  exact ⟨inner, heap, scalar, entry.identity, rows, after, inner_open, skipped, checked,
    read_ready checked scalar (headGrowth scalar) after_properties.2.1 available warm_support initial_fits (headGrowth_ge scalar), stable⟩
end MicroCFTA.OpenReadKernels

#print axioms MicroCFTA.OpenReadKernels.constructed_open_mu
#check @MicroCFTA.OpenReadKernels.constructed_open_mu
#print MicroCFTA.OpenReadKernels.constructed_open_mu
#print axioms MicroCFTA.OpenReadKernels.produced_visited_and_replay
#check @MicroCFTA.OpenReadKernels.produced_visited_and_replay
#print MicroCFTA.OpenReadKernels.produced_visited_and_replay
