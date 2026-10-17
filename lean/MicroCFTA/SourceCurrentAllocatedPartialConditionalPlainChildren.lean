import MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainSupport
import MicroCFTA.SourceCurrentAllocatedPartialPlainInputs
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

/-!
# Mixed-table Region children from smaller node calls

These are induction helpers. Their Below premise applies only to strictly
smaller node ranks. The root rank induction must derive that premise.
Each indexed child uses the actual descended equality payload and current
caller. Completed child frames restore the original active-owner bound
before the suffix. No future result or native range plan is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainChildren
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveOrder (nodeRank)
open SourceCurrentAllocatedPartialConditionalPlainSupport (Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Smaller actual node calls construct the literal indexed walk in source order. -/
theorem walk
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
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧ Stored after := by
  induction values generalizing index inventory before memos with
  | nil =>
      refine ⟨[], before, inventory, memos, .nil, .nil,
        SourceCurrentAllocatedPartialChecksComposition.walk_nil, Post.refl initial, ?_, stored⟩
      intro value absent
      cases absent
  | cons first rest tailIH =>
      cases regions with
      | cons firstRegion restRegions =>
          obtain ⟨descent, descentPost, prefixStored, prefixActive⟩ :=
            SourceCurrentAllocatedPartialConditionalPlainSupport.descent formulas solver inventory before memos
              initial combined index inheritedReady stored active
          have firstAvailable := available first List.mem_cons_self
          have childSmall : nodeRank ⟨(descend before combined index).1, first⟩ < rank :=
            smaller first List.mem_cons_self
          have childActive : ActiveAbove (nodeRank ⟨(descend before combined index).1, first⟩)
              (descend before combined index).2 := SourceCurrentAllocatedPartialConditionalFrames.active_mono prefixActive (by omega)
          obtain ⟨result, middle, stepInventory, stepMemos, head, headReads, headChecks,
              headPost, resultAvailable, headStored, _⟩ :=
            ih ⟨(descend before combined index).1, first⟩ childSmall descentPost.context descent.inherited
              (descentPost.effects.keeps.available first firstAvailable) firstRegion prefixStored childActive
          have firstPost := descentPost.trans headPost
          have nextInherited := inheritedReady.grows firstPost.effects.grows.constraint_growth
          have nextAvailable : Values middle.checked.native.machine.heap rest :=
            fun value member => firstPost.effects.keeps.available value
              (available value (List.mem_cons_of_mem _ member))
          have nextActive : ActiveAbove (rank - 1) middle :=
            SourceCurrentAllocatedPartialConditionalFrames.node_call head prefixActive
          obtain ⟨results, after, next, final, tail, tailReads, tailChecks, tailPost, tailAvailable, tailStored⟩ :=
            tailIH (index + 1) headPost.context nextInherited nextAvailable restRegions
              (fun value member => smaller value (List.mem_cons_of_mem _ member)) headStored nextActive
          refine ⟨result :: results, after, next, final, .cons head tail, .cons headReads tailReads,
            SourceCurrentAllocatedPartialChecksComposition.walk_cons head tail headChecks tailChecks,
            firstPost.trans tailPost, ?_, tailStored⟩
          intro value member
          rcases List.mem_cons.mp member with same | later
          · subst value
            exact tailPost.effects.keeps.available result resultAvailable
          · exact tailAvailable value later

/-- Contradiction skips children; live payloads use the smaller-rank walk helper. -/
theorem children
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (values : List Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (regions : Regions values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank (width := width)) :
    ∃ results after next final, ∃ actual : Children budget combined values before results after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧ Stored after := by
  cases combined with
  | contradiction =>
      exact ⟨EqualityLeafProjectionRuntimeEmpty.erase values, before, inventory, memos, .contradiction,
        .contradiction, SourceCurrentAllocatedPartialChecksComposition.children_contradiction,
        Post.refl initial, (SourceEqualityEmptyPropagation.erased_scope before.checked.native.machine.heap values).1, stored⟩
  | live identity records =>
      obtain ⟨results, after, next, final, actual, reads, checks, post, available, stored⟩ :=
        walk formulas solver budget rank (.live identity records) 0 values initial inheritedReady available
          regions smaller stored active ih
      exact ⟨results, after, next, final, .live actual, .live reads,
        SourceCurrentAllocatedPartialChecksComposition.children_live actual checks, post, available, stored⟩

end MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainChildren
