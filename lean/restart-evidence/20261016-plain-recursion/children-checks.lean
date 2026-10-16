import MicroCFTA.SourceCurrentAllocatedPartialPlainChildren

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainChildren.walk
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainChildren.walk
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainChildren.children
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainChildren.children

namespace PlainChildrenChecks
open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialPlainRecursionDefs (Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

theorem constructed_walk_has_independent_language_and_active_bound
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (index : Nat) (values : List Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (regions : Regions values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank (width := width)) :
    ∃ results after next final, ∃ actual : Walk budget combined index values before results after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      Stored after ∧ SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual ∧
      results.length = values.length ∧ ActiveAbove (rank - 1) after := by
  obtain ⟨results, after, next, final, actual, reads, checks, post, availableOut, storedOut⟩ :=
    SourceCurrentAllocatedPartialPlainChildren.walk formulas solver budget rank combined index values
      initial inheritedReady available regions smaller stored active ih
  obtain ⟨_, _, _, law⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver reads inventory
    checks initial inheritedReady available
  exact ⟨results, after, next, final, actual, reads, checks, post, availableOut, storedOut, law,
    actual.length, (SourceCurrentAllocatedPartialActiveFrames.walk actual).activeExcept active⟩

theorem constructed_children_narrows_and_preserves_satisfied_parent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (first second : Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap [first, second])
    (regions : Regions [first, second])
    (firstSmaller : nodeRank ⟨combined, first⟩ < rank) (secondSmaller : nodeRank ⟨combined, second⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank (width := width)) :
    ∃ results after next final, ∃ actual : Children budget combined [first, second] before results after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual) ∧
      Post formulas solver next before after final ∧ Stored after ∧ results.length = 2 ∧
      ∀ ambient symbol terms,
        (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) [first, second] terms) ∧
        (SourceEqualityPrecheck.Sat (.node symbol terms) combined.payload →
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) [first, second] terms →
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms) := by
  have smaller : ∀ value ∈ [first, second], nodeRank ⟨combined, value⟩ < rank := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstSmaller
    · exact secondSmaller
  obtain ⟨results, after, next, final, actual, reads, checks, post, _, storedOut⟩ :=
    SourceCurrentAllocatedPartialPlainChildren.children formulas solver budget rank combined [first, second]
      initial inheritedReady available regions smaller stored active ih
  obtain ⟨_, _, _, law⟩ := SourceCurrentAllocatedPartialActual.children formulas solver reads inventory
    checks initial inheritedReady available
  refine ⟨results, after, next, final, actual, reads, checks, post, storedOut, actual.length, ?_⟩
  intro ambient symbol terms
  exact ⟨law.narrows ambient terms, law.preserves ambient symbol terms⟩

theorem empty_walk_needs_no_child_completion
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (combined : EqValue) (index : Nat)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (stored : Stored before) (active : ActiveAbove 0 before) :
    ∃ next, Post formulas solver next before before memos ∧ Stored before ∧
      Checks (walkTrace (Walk.nil (budget := budget) (combined := combined) (index := index) (before := before))) := by
  have smaller : ∀ value ∈ ([] : List Node), nodeRank ⟨combined, value⟩ < 0 := by
    intro value absent
    cases absent
  have ih : Below formulas solver budget 0 (width := width) := by
    intro inventory before memos request impossible
    exact False.elim (Nat.not_lt_zero _ impossible)
  obtain ⟨results, after, next, final, actual, reads, checks, post, _, storedOut⟩ :=
    SourceCurrentAllocatedPartialPlainChildren.walk formulas solver budget 0 combined index [] initial
      inheritedReady (fun _ absent => nomatch absent) .nil smaller stored active ih
  cases actual
  cases reads
  exact ⟨next, post, storedOut, checks⟩

end PlainChildrenChecks

#print axioms PlainChildrenChecks.constructed_walk_has_independent_language_and_active_bound
#check @PlainChildrenChecks.constructed_walk_has_independent_language_and_active_bound
#print axioms PlainChildrenChecks.constructed_children_narrows_and_preserves_satisfied_parent
#check @PlainChildrenChecks.constructed_children_narrows_and_preserves_satisfied_parent
#print axioms PlainChildrenChecks.empty_walk_needs_no_child_completion
#check @PlainChildrenChecks.empty_walk_needs_no_child_completion
