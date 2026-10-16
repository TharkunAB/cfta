import MicroCFTA.SourceCurrentAllocatedPartialPlainChildren

/-!
# Current plain row completion under smaller node calls

The list helpers use a bounded node induction hypothesis. Each row runs
its own finite edge call, then its returned-edge descendants and suffix.
Every prefix derives the actual next Context and structural stored domain.
The public node theorem must discharge the bounded hypothesis.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainRows
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open SourceCurrentAllocatedPartialPlainRecursionDefs (Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Returned child Regions and smaller ranks construct the literal descendant continuation. -/
theorem descendants
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (regions : SourceEqualityPartialPlainRegion.Children edge.children)
    (smaller : ∀ value ∈ edge.children, nodeRank ⟨inherited, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank) :
    ∃ result after next final, ∃ actual : Descendants budget inherited edge before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧ Stored after := by
  obtain ⟨combined, prefix, prefixPost, prefixStored, prefixActive⟩ :=
    SourceCurrentAllocatedPartialPlainPrefixes.inherited_prefix formulas solver inventory before memos initial
      edge inherited resident inheritedReady stored active
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have prefixAvailable : Values (prefixState before edge inherited).checked.native.machine.heap edge.children :=
    fun value member => prefixPost.effects.keeps.available _ (available value member)
  obtain ⟨results, middle, childInventory, final, children, reads, checks, childPost, _available, childStored⟩ :=
    SourceCurrentAllocatedPartialPlainChildren.children formulas solver budget rank combined edge.children
      prefixPost.context prefix.combinedReady prefixAvailable regions smaller prefixStored prefixActive ih
  let actual := Descendants.run prefix.actual children
  have actualReads : DescendantsReads formulas solver actual memos final := .run reads
  have actualChecks := SourceCurrentAllocatedPartialChecksComposition.descendants_run prefix.actual children checks
  obtain ⟨next, post, resultResident, _law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver
    actualReads inventory actualChecks initial inheritedReady resident
  exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, resultResident,
    childStored.advance _ middle.fourth middle.merge⟩

/-- Ordered source rows construct their own edge calls and returned-child recursion. -/
theorem rows
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edges : List Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap edges)
    (regions : SourceEqualityPartialPlainRegion.Rows edges)
    (smaller : ∀ edge ∈ edges, edgeRank ⟨inherited, edge⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below formulas solver budget rank) :
    ∃ results after next final, ∃ actual : Rows budget inherited edges before results after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
      Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧ Stored after := by
  cases regions with
  | nil =>
      exact ⟨[], before, inventory, memos, .nil, .nil,
        SourceCurrentAllocatedPartialChecksComposition.rows_nil, Post.refl initial,
        (by intro edge member; cases member), stored⟩
  | @cons original originals physical children regions =>
      have originalSmaller := smaller original List.mem_cons_self
      have edgeActive : ActiveAbove (edgeRank ⟨inherited, original⟩) before := active.mono (by omega)
      obtain ⟨narrowed, middle, edgeInventory, edgeMemos, _stable, edgeCall, edgeReads, edgeChecks,
        edgePost, narrowedResident, edgeStored, shape, _edgeLaw⟩ :=
        SourceCurrentAllocatedPartialPlainEdgeCall.finite formulas solver budget ⟨inherited, original⟩ initial
          inheritedReady (resident original List.mem_cons_self)
          (fun _ => SourceCurrentAllocatedPartialPlainInputs.own_empty _ physical) stored edgeActive
      have childSmaller : ∀ value ∈ narrowed.children, nodeRank ⟨inherited, value⟩ < rank := by
        intro value member
        have lower := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited narrowed value member
        have height := shape.height
        simp only [edgeRank] at lower originalSmaller
        omega
      obtain ⟨result, afterChildren, childInventory, childMemos, childCall, childReads, childChecks,
        childPost, _resultResident, childStored⟩ := descendants formulas solver budget rank inherited narrowed
          edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
          (shape.regions children) childSmaller edgeStored
          ((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeCall).activeExcept active) ih
      have firstPost := edgePost.trans childPost
      have tailResident : Edges afterChildren.checked.native.machine.heap originals := fun edge member =>
        edge_grows _ _ firstPost.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, next, final, tail, tailReads, tailChecks, tailPost, _resultsResident, tailStored⟩ :=
        rows formulas solver budget rank inherited originals childPost.context
          (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident regions
          (fun edge member => smaller edge (List.mem_cons_of_mem _ member)) childStored
          ((SourceCurrentAllocatedPartialActiveFrames.descendants childCall).activeExcept
            ((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeCall).activeExcept active)) ih
      let actual := Rows.cons edgeCall childCall tail
      have actualReads : RowsReads formulas solver actual memos final := .cons edgeReads childReads tailReads
      have actualChecks := SourceCurrentAllocatedPartialChecksComposition.rows_cons edgeCall childCall tail
        edgeChecks childChecks tailChecks
      obtain ⟨next, post, resultsResident, _law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver
        actualReads inventory actualChecks initial inheritedReady resident
      exact ⟨result :: results, after, next, final, actual, actualReads, actualChecks, post, resultsResident, tailStored⟩
termination_by edges.length

end MicroCFTA.SourceCurrentAllocatedPartialPlainRows
