import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceChildren
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge

/-!
# Ordinary rows from initial constructor headroom

Each original row first constructs its parent result.
Its actual Work leaves capacity for the returned descendants.
The descendant Work then leaves capacity for the original row suffix.
Only smaller node ranks enter the induction interface.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRows
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Below)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (RowsShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height edgeHeight edgesHeight)
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Returned domain children and smaller calls construct the literal descendant continuation. -/
theorem descendants
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge) (domain : DEdge edge)
    (smaller : ∀ value ∈ edge.children, nodeRank ⟨inherited, value⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below bits formulas solver budget rank)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity edge)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits edge)
    (heightBound : edgeHeight edge ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound)) :
    ∃ result after next final, ∃ actual : Descendants budget inherited edge before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ EdgeNarrow edge result := by
  obtain ⟨combined, prefixReceipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory
    edge inherited before.checked initial.ready initial.admitted resident inheritedReady
  have prefixPost := (SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
    initial edge inherited combined resident inheritedReady prefixReceipt.actual).2
  have prefixStored : Stored (prefixState before edge inherited) := stored.advancePhysical _
  have prefixActive := active.advance
    (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited) before.fourth before.merge
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have prefixAvailable : Values (prefixState before edge inherited).checked.native.machine.heap edge.children :=
    fun value member => prefixPost.effects.keeps.available _ (available value member)
  have childrenRoom : Headroom bits (prefixState before edge inherited).checked.native.machine.heap
      (edge.children.length * nodeNodes rows arity limits bound)
      (edge.children.length * nodeEdges rows arity limits bound) := by
    change Headroom bits before.checked.native.machine.heap _ _
    apply room.mono
    · exact Nat.mul_le_mul_right _ (EdgeShape.arity edge profile)
    · have enough := Nat.mul_le_mul_right (nodeEdges rows arity limits bound) (EdgeShape.arity edge profile)
      change edge.children.length * nodeEdges rows arity limits bound ≤ 1 + arity * nodeEdges rows arity limits bound
      omega
  obtain ⟨results, middle, _childInventory, final, children, reads, checks, _childPost, _available, _childStored, _related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceChildren.children formulas solver budget rank combined edge.children
      prefixPost.context prefixReceipt.combinedReady prefixAvailable domain smaller prefixStored prefixActive ih
      rows arity bound limits (EdgeShape.children edge profile)
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge guards)
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using heightBound) childrenRoom
  let actual := Descendants.run prefixReceipt.actual children
  have actualReads : DescendantsReads formulas solver actual memos final := .run (combined := prefixReceipt.actual) reads
  have actualChecks := SourceCurrentAllocatedPartialChecksComposition.descendants_run prefixReceipt.actual children checks
  obtain ⟨next, post, resultResident, _law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver
    actualReads inventory actualChecks initial inheritedReady resident
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.descendants formulas solver actualReads inventory
    initial inheritedReady resident domain stored
  exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, resultResident, produced.1, produced.2.1⟩

/-- Ordered rows derive every parent call, descendant continuation, and positional bound. -/
theorem rows
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edges : List Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap edges) (domain : DRows edges)
    (smaller : ∀ edge ∈ edges, edgeRank ⟨inherited, edge⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (ih : Below bits formulas solver budget rank)
    (rowLimit arity bound : Nat) (limits : Limits) (profile : RowsShape rowLimit arity edges)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits edges)
    (heightBound : edgesHeight edges ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (edges.length * rowNodes rowLimit arity limits bound) (edges.length * rowEdges rowLimit arity limits bound)) :
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
      have originalHeight : edgeHeight original ≤ bound := by
        change max (edgeHeight original) (edgesHeight originals) ≤ bound at heightBound
        omega
      have tailHeight : edgesHeight originals ≤ bound := by
        change max (edgeHeight original) (edgesHeight originals) ≤ bound at heightBound
        omega
      let childNodes := descendantsNodes (parentRows limits rowLimit arity bound) (max arity 1) (parentGuards limits) bound
      let childEdges := descendantsEdges (parentRows limits rowLimit arity bound) (max arity 1) (parentGuards limits) bound
      have splitRoom : Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rowLimit arity bound + (childNodes + originals.length * rowNodes rowLimit arity limits bound))
          (edgeBudget limits rowLimit arity bound + (childEdges + originals.length * rowEdges rowLimit arity limits bound)) := by
        apply room.mono
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowNodes, childNodes, descendantsNodes]
          omega
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowEdges, childEdges, descendantsEdges]
          omega
      have edgeRoom := splitRoom.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      obtain ⟨narrowed, middle, _edgeInventory, edgeMemos, _stable, edgeCall, edgeReads, edgeChecks,
        edgePost, narrowedResident, edgeStored, narrow, certificate, _edgeLaw⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge.finite bits formulas solver budget ⟨inherited, original⟩ initial
          inheritedReady (resident original List.mem_cons_self) originalDomain stored edgeActive
          rowLimit arity bound limits profile.1 guards.1 originalHeight edgeRoom
      have edgeWork := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.edge_call formulas solver edgeReads inventory
        initial inheritedReady (resident original List.mem_cons_self) originalDomain stored
        rowLimit arity bound limits profile.1 guards.1 originalHeight
      have remaining := splitRoom.after edgeWork
      have narrowedProfile := certificate rowLimit arity bound limits profile.1 guards.1 originalHeight
      have descendantsRoom := remaining.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
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
          (parentRows limits rowLimit arity bound) (max arity 1) bound (parentGuards limits)
          narrowedProfile.1 narrowedProfile.2 (Nat.le_trans narrow.2 originalHeight) descendantsRoom
      have childWork := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.descendants formulas solver childReads
        _edgeInventory edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth)
        narrowedResident narrow.1 edgeStored (parentRows limits rowLimit arity bound) (max arity 1) bound
        (parentGuards limits) narrowedProfile.1 narrowedProfile.2 (Nat.le_trans narrow.2 originalHeight)
      have tailRoom := remaining.after childWork
      have firstPost := edgePost.trans childPost
      have tailResident : Edges afterChildren.checked.native.machine.heap originals := fun edge member =>
        edge_grows _ _ firstPost.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, _tailInventory, final, tail, tailReads, tailChecks, _tailPost, _resultsResident, tailStored, tailBounds⟩ :=
        rows budget rank inherited originals childPost.context
          (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident restDomain
          (fun edge member => smaller edge (List.mem_cons_of_mem _ member)) childStored
          ((SourceCurrentAllocatedPartialActiveFrames.descendants childCall).activeExcept
            ((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeCall).activeExcept active)) ih
          rowLimit arity bound limits profile.2 guards.2 tailHeight tailRoom
      let actual := Rows.cons edgeCall childCall tail
      have actualReads : RowsReads formulas solver actual memos final := .cons edgeReads childReads tailReads
      have actualChecks := SourceCurrentAllocatedPartialChecksComposition.rows_cons edgeCall childCall tail
        edgeChecks childChecks tailChecks
      obtain ⟨next, post, resultsResident, _law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver
        actualReads inventory actualChecks initial inheritedReady resident
      exact ⟨result :: results, after, next, final, actual, actualReads, actualChecks, post, resultsResident, tailStored,
        .cons (SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_trans narrow childNarrow) tailBounds⟩
termination_by edges.length

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRows
