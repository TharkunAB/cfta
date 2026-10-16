import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs
import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

/-!
# Current constrained child construction from smaller node calls

These are induction helpers. Their Below premise applies only to strictly
smaller node ranks. The root rank induction must derive that premise.
Each indexed child uses the actual descended equality payload and current
caller. Completed child frames restore the original active-owner bound
before the suffix. The rooted plan contains only ranges at causally reached machine entries.
The root strong induction must discharge the smaller-node interface.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterChildren
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs (Below)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Plan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Smaller actual node calls construct the literal indexed walk in source order. -/
theorem walk
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (index : Nat) (values : List Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank (width := width))
    (plan : Plan budget (.walk combined index values before)) :
    ∃ results after next final, ∃ actual : Walk budget combined index values before results after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧ Stored after ∧ All₂ NodeNarrow values results := by
  induction values generalizing index inventory before memos with
  | nil =>
      refine ⟨[], before, inventory, memos, .nil, .nil,
        SourceCurrentAllocatedPartialChecksComposition.walk_nil, Post.refl initial, ?_, stored, .nil⟩
      intro value absent
      cases absent
  | cons first rest tailIH =>
      cases domain with
      | cons firstDomain restDomain =>
          obtain ⟨descent, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver
            inventory before memos initial combined index inheritedReady
          have prefixStored := stored.descend combined index
          have prefixActive := active.advance (descend before combined index).2.checked before.fourth before.merge
          have firstAvailable := available first List.mem_cons_self
          have childSmall : nodeRank ⟨(descend before combined index).1, first⟩ < rank :=
            smaller first List.mem_cons_self
          have childActive : ActiveAbove (nodeRank ⟨(descend before combined index).1, first⟩)
              (descend before combined index).2 := prefixActive.mono (by omega)
          obtain ⟨result, middle, stepInventory, stepMemos, head, headReads, headChecks,
              headPost, resultAvailable, headStored, headBound, _⟩ :=
            ih ⟨(descend before combined index).1, first⟩ childSmall descentPost.context descent.inherited
              (descentPost.effects.keeps.available first firstAvailable) firstDomain prefixStored childActive
              (plan.restrict (.direct .walk_node))
          have firstPost := descentPost.trans headPost
          have nextInherited := inheritedReady.grows firstPost.effects.grows.constraint_growth
          have nextAvailable : Values middle.checked.native.machine.heap rest :=
            fun value member => firstPost.effects.keeps.available value
              (available value (List.mem_cons_of_mem _ member))
          have nextActive : ActiveAbove (rank - 1) middle :=
            (SourceCurrentAllocatedPartialActiveFrames.node_call head).activeExcept prefixActive
          obtain ⟨results, after, next, final, tail, tailReads, tailChecks, tailPost, tailAvailable, tailStored, tailBounds⟩ :=
            tailIH (index + 1) headPost.context nextInherited nextAvailable restDomain
              (fun value member => smaller value (List.mem_cons_of_mem _ member)) headStored nextActive
              (plan.restrict (.direct (.walk_tail head)))
          refine ⟨result :: results, after, next, final, .cons head tail, .cons headReads tailReads,
            SourceCurrentAllocatedPartialChecksComposition.walk_cons head tail headChecks tailChecks,
            firstPost.trans tailPost, ?_, tailStored, .cons headBound tailBounds⟩
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
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank (width := width))
    (plan : Plan budget (.children combined values before)) :
    ∃ results after next final, ∃ actual : Children budget combined values before results after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧ Stored after ∧ All₂ NodeNarrow values results := by
  cases combined with
  | contradiction =>
      exact ⟨EqualityLeafProjectionRuntimeEmpty.erase values, before, inventory, memos, .contradiction,
        .contradiction, SourceCurrentAllocatedPartialChecksComposition.children_contradiction,
        Post.refl initial, (SourceEqualityEmptyPropagation.erased_scope before.checked.native.machine.heap values).1, stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values⟩
  | live identity records =>
      obtain ⟨results, after, next, final, actual, reads, checks, post, available, stored, related⟩ :=
        walk formulas solver budget rank (.live identity records) 0 values initial inheritedReady available
          domain smaller stored active ih (plan.restrict (.direct .children_live))
      exact ⟨results, after, next, final, .live actual, .live reads,
        SourceCurrentAllocatedPartialChecksComposition.children_live actual checks, post, available, stored, related⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterChildren
