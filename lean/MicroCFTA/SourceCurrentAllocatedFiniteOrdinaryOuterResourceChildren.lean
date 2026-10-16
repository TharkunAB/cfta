import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs
import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

/-!
# Child construction from initial constructor headroom

Only smaller node ranks enter the induction interface.
Each completed child supplies its actual allocation bound.
That bound reserves capacity for the original ordered suffix.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceChildren
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Below)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers (nodeNodes nodeEdges)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

/-- Smaller actual node calls construct the literal indexed walk in source order. -/
theorem walk
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (index : Nat) (values : List Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below bits formulas solver budget rank)
    (rows arity bound : Nat) (limits : Limits)
    (profile : ChildrenShape rows arity values)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits values)
    (heightBound : childrenHeight values ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)) :
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
          have prefixStored := stored.advancePhysical
            (SourceCurrentAllocatedNativeEffects.physical (descend before combined index).2.checked)
          have prefixActive := active.advance (descend before combined index).2.checked before.fourth before.merge
          have firstAvailable := available first List.mem_cons_self
          have childSmall : nodeRank ⟨(descend before combined index).1, first⟩ < rank :=
            smaller first List.mem_cons_self
          have childActive : ActiveAbove (nodeRank ⟨(descend before combined index).1, first⟩)
              (descend before combined index).2 := prefixActive.mono (by omega)
          have firstHeight : height first ≤ bound := by
            change max (height first) (childrenHeight rest) ≤ bound at heightBound
            omega
          have restHeight : childrenHeight rest ≤ bound := by
            change max (height first) (childrenHeight rest) ≤ bound at heightBound
            omega
          have splitRoom : Headroom bits (descend before combined index).2.checked.native.machine.heap
              (nodeNodes rows arity limits bound + rest.length * nodeNodes rows arity limits bound)
              (nodeEdges rows arity limits bound + rest.length * nodeEdges rows arity limits bound) := by
            change Headroom bits before.checked.native.machine.heap _ _
            exact room.mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
              (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
          have headRoom := splitRoom.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          obtain ⟨result, middle, _stepInventory, stepMemos, head, headReads, headChecks,
              headPost, resultAvailable, headStored, headBound, _⟩ :=
            ih ⟨(descend before combined index).1, first⟩ childSmall descentPost.context descent.inherited
              (descentPost.effects.keeps.available first firstAvailable) firstDomain prefixStored childActive
              rows arity bound limits profile.1 guards.1 firstHeight headRoom
          have firstPost := descentPost.trans headPost
          have nextInherited := inheritedReady.grows firstPost.effects.grows.constraint_growth
          have nextAvailable : Values middle.checked.native.machine.heap rest :=
            fun value member => firstPost.effects.keeps.available value
              (available value (List.mem_cons_of_mem _ member))
          have nextActive : ActiveAbove (rank - 1) middle :=
            (SourceCurrentAllocatedPartialActiveFrames.node_call head).activeExcept prefixActive
          have headWork := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.node_call formulas solver headReads
            inventory descentPost.context descent.inherited
            (descentPost.effects.keeps.available first firstAvailable) firstDomain prefixStored
            rows arity bound limits profile.1 guards.1 firstHeight
          have tailRoom := splitRoom.after headWork
          obtain ⟨results, after, next, final, tail, tailReads, tailChecks, tailPost, tailAvailable, tailStored, tailBounds⟩ :=
            tailIH (index + 1) headPost.context nextInherited nextAvailable restDomain
              (fun value member => smaller value (List.mem_cons_of_mem _ member)) headStored nextActive
              profile.2 guards.2 restHeight tailRoom
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
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget rank : Nat) (combined : EqValue) (values : List Node)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below bits formulas solver budget rank)
    (rows arity bound : Nat) (limits : Limits)
    (profile : ChildrenShape rows arity values)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits values)
    (heightBound : childrenHeight values ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)) :
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
          domain smaller stored active ih rows arity bound limits profile guards heightBound room
      exact ⟨results, after, next, final, .live actual, .live reads,
        SourceCurrentAllocatedPartialChecksComposition.children_live actual checks, post, available, stored, related⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceChildren
