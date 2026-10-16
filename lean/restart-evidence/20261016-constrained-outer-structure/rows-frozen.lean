import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterChildren

/-!
# Constructed constrained finite ordinary rows and descendants

These helpers use only strictly smaller node calls through Below.
Each row constructs its current edge call before its returned descendants.
The range plan restricts through actual completed earlier prefixes.
Inherited allocation and raw rebuilding retain the same complete caller.
Ordered results retain domain and height bounds at every source position.
The root node rank induction must discharge Below.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRows
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs (Below)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Plan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Returned domain children and smaller calls construct the literal descendant continuation. -/
theorem descendants
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge) (domain : DEdge edge)
    (smaller : ∀ value ∈ edge.children, nodeRank ⟨inherited, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below (width := width) formulas solver budget rank)
    (plan : Plan budget (.descendants inherited edge before)) :
    ∃ result after next final, ∃ actual : Descendants budget inherited edge before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ EdgeNarrow edge result := by
  obtain ⟨combined, prefixReceipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory
    edge inherited before.checked initial.ready initial.admitted resident inheritedReady
  have prefixPost := (SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
    initial edge inherited combined resident inheritedReady prefixReceipt.actual).2
  have prefixStored := stored.prefixState edge inherited
  have prefixActive := active.advance
    (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited) before.fourth before.merge
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have prefixAvailable : Values (prefixState before edge inherited).checked.native.machine.heap edge.children :=
    fun value member => prefixPost.effects.keeps.available _ (available value member)
  obtain ⟨results, middle, _childInventory, final, children, reads, checks, _childPost, _available, _childStored, _related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterChildren.children formulas solver budget rank combined edge.children
      prefixPost.context prefixReceipt.combinedReady prefixAvailable domain smaller prefixStored prefixActive ih
      (plan.restrict (.direct (.descendants_children prefixReceipt.actual)))
  let actual := Descendants.run prefixReceipt.actual children
  have actualReads : DescendantsReads formulas solver actual memos final := .run (combined := prefixReceipt.actual) reads
  have actualChecks := SourceCurrentAllocatedPartialChecksComposition.descendants_run prefixReceipt.actual children checks
  obtain ⟨next, post, resultResident, _law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver
    actualReads inventory actualChecks initial inheritedReady resident
  have structural := SourceCurrentAllocatedFiniteOrdinaryOuterActual.descendants formulas solver actualReads inventory
    actualChecks initial inheritedReady resident domain stored
  exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, resultResident, structural⟩

/-- Ordered rows derive every parent call, descendant continuation, and positional bound. -/
theorem rows
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edges : List Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap edges) (domain : DRows edges)
    (smaller : ∀ edge ∈ edges, edgeRank ⟨inherited, edge⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below (width := width) formulas solver budget rank)
    (plan : Plan budget (.rows inherited edges before)) :
    ∃ results after next final, ∃ actual : Rows budget inherited edges before results after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
      Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧
      Stored after ∧ All₂ EdgeNarrow edges results := by
  cases domain with
  | nil =>
      exact ⟨[], before, inventory, memos, .nil, .nil,
        SourceCurrentAllocatedPartialChecksComposition.rows_nil, Post.refl initial,
        (by intro edge member; cases member), stored, .nil⟩
  | @cons originals original originalDomain restDomain =>
      have originalSmaller := smaller original List.mem_cons_self
      have edgeActive : ActiveAbove (edgeRank ⟨inherited, original⟩) before := active.mono (by omega)
      obtain ⟨narrowed, middle, _edgeInventory, edgeMemos, _stable, edgeCall, edgeReads, edgeChecks,
        edgePost, narrowedResident, edgeStored, narrow, _edgeLaw⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.finite formulas solver budget ⟨inherited, original⟩ initial
          inheritedReady (resident original List.mem_cons_self) originalDomain stored edgeActive
          (plan.restrict (.direct .rows_edge)).edge_call_ranges
      have childSmaller : ∀ value ∈ narrowed.children, nodeRank ⟨inherited, value⟩ < rank := by
        intro value member
        have lower := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited narrowed value member
        have height := narrow.2
        change MergedOrdinaryHeight.edgeHeight narrowed ≤ MergedOrdinaryHeight.edgeHeight original at height
        change nodeRank ⟨inherited, value⟩ < 2 * (MergedOrdinaryHeight.edgeHeight narrowed + 1) at lower
        change 2 * (MergedOrdinaryHeight.edgeHeight original + 1) < rank at originalSmaller
        omega
      obtain ⟨result, afterChildren, _childInventory, childMemos, childCall, childReads, childChecks,
        childPost, _resultResident, childStored, childNarrow⟩ := descendants formulas solver budget rank inherited narrowed
          edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident narrow.1
          childSmaller edgeStored ((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeCall).activeExcept active) ih
          (plan.restrict (.direct (.rows_descendants edgeCall)))
      have firstPost := edgePost.trans childPost
      have tailResident : Edges afterChildren.checked.native.machine.heap originals := fun edge member =>
        edge_grows _ _ firstPost.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, _tailInventory, final, tail, tailReads, tailChecks, _tailPost, _resultsResident, tailStored, tailBounds⟩ :=
        rows budget rank inherited originals childPost.context
          (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident restDomain
          (fun edge member => smaller edge (List.mem_cons_of_mem _ member)) childStored
          ((SourceCurrentAllocatedPartialActiveFrames.descendants childCall).activeExcept
            ((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeCall).activeExcept active)) ih
          (plan.restrict (.direct (.rows_tail edgeCall childCall)))
      let actual := Rows.cons edgeCall childCall tail
      have actualReads : RowsReads formulas solver actual memos final := .cons edgeReads childReads tailReads
      have actualChecks := SourceCurrentAllocatedPartialChecksComposition.rows_cons edgeCall childCall tail
        edgeChecks childChecks tailChecks
      obtain ⟨next, post, resultsResident, _law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver
        actualReads inventory actualChecks initial inheritedReady resident
      exact ⟨result :: results, after, next, final, actual, actualReads, actualChecks, post, resultsResident, tailStored,
        .cons (SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_trans narrow childNarrow) tailBounds⟩
termination_by edges.length

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRows
