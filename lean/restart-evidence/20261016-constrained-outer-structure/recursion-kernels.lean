import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterChildren

namespace FiniteOrdinaryOuterRecursionChecks
open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs (Below)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Plan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- An empty walk constructs its own exact identity return with no smaller-call hypothesis. -/
theorem zero_rank_empty_walk (budget : Nat) (inventory : Inventory) (before : Caller width) (memos : Memos)
    (combined : EqValue) (index : Nat) (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints combined) (stored : Stored before)
    (active : ActiveAbove 0 before) (plan : Plan budget (.walk combined index [] before)) :
    ∃ next, Post formulas solver next before before memos ∧ Stored before := by
  have below : Below (width := width) formulas solver budget 0 := by
    intro currentInventory current globals request impossible
    exact False.elim ((Nat.not_lt_zero _) impossible)
  obtain ⟨results, after, next, final, actual, reads, _checks, post, _available, retained, _related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterChildren.walk formulas solver budget 0 combined index [] initial ready
      (by intro value absent; cases absent) .nil (by intro value absent; cases absent) stored active below plan
  cases actual
  cases reads
  exact ⟨next, post, retained⟩

/-- The same constructed walk has positional bounds and the independent language law from its actual reads. -/
theorem walk_semantic_structure (budget rank : Nat) (combined : EqValue) (index : Nat) (values : List Node)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (ready : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values)
    (smaller : ∀ value ∈ values, nodeRank ⟨combined, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below (width := width) formulas solver budget rank) (plan : Plan budget (.walk combined index values before)) :
    ∃ results after next final, ∃ actual : Walk budget combined index values before results after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      Stored after ∧ All₂ NodeNarrow values results ∧ SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual := by
  obtain ⟨results, after, next, final, actual, reads, checks, post, resident, retained, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterChildren.walk formulas solver budget rank combined index values initial ready available
      domain smaller stored active ih plan
  obtain ⟨_semanticInventory, _semanticPost, _semanticValues, language⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver reads
    inventory checks initial ready available
  exact ⟨results, after, next, final, actual, reads, checks, post, resident, retained, related, language⟩

#print axioms zero_rank_empty_walk
#check @zero_rank_empty_walk
#print axioms walk_semantic_structure
#check @walk_semantic_structure
end FiniteOrdinaryOuterRecursionChecks
