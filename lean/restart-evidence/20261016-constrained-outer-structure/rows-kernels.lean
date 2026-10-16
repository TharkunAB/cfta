import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode
namespace FiniteOrdinaryOuterRowsKernels
open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
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

private theorem below (budget rank : Nat) : Below (width := width) formulas solver budget rank := by
  intro inventory before memos request _smaller initial inherited available domain stored active plan
  obtain ⟨result, after, next, final, _stable, actual, reads, checks, post, output, retained, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterNode.finite formulas solver budget request initial inherited available
      domain stored active plan
  exact ⟨result, after, next, final, actual, reads, checks, post, output, retained, narrow, law⟩

/-- The node rank theorem discharges every smaller call in actual ordered row construction. -/
theorem constructed_rows
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edges : List Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap edges) (domain : DRows edges)
    (smaller : ∀ edge ∈ edges, edgeRank ⟨inherited, edge⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (plan : Plan budget (.rows inherited edges before)) :
    ∃ results after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.rows f g s r e p h m c n budget inherited edges before)
        results after ∧
      ∃ actual : Rows budget inherited edges before results after,
        RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
        Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧
        Stored after ∧ All₂ EdgeNarrow edges results ∧ results.length = edges.length ∧
        ActiveAbove (rank - 1) after ∧ SourceCurrentAllocatedPartialForestLanguage.RowsLaw formulas solver actual := by
  obtain ⟨results, after, next, final, actual, reads, checks, post, residentAfter, storedAfter, narrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterRows.rows formulas solver budget rank inherited edges initial
      inheritedReady resident domain smaller stored active (below formulas solver budget rank) plan
  obtain ⟨_lawInventory, _lawPost, _resident, law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver reads
    inventory checks initial inheritedReady resident
  exact ⟨results, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.rows_complete actual,
    actual, reads, checks, post, residentAfter, storedAfter, narrow, actual.length,
    (SourceCurrentAllocatedPartialActiveFrames.rows actual).activeExcept active, law⟩

/-- Actual descendants derive their source guard law and stable literal return without a completion callback. -/
theorem constructed_descendants
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge) (domain : DEdge edge)
    (smaller : ∀ child ∈ edge.children, nodeRank ⟨inherited, child⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before)
    (plan : Plan budget (.descendants inherited edge before)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.descendants f g s r e p h m c n budget inherited edge before)
        result after ∧
      ∃ actual : Descendants budget inherited edge before result after,
        DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ EdgeNarrow edge result ∧ ActiveAbove (rank - 1) after ∧
        SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver ⟨inherited, edge⟩ result := by
  obtain ⟨result, after, next, final, actual, reads, checks, post, residentAfter, storedAfter, narrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterRows.descendants formulas solver budget rank inherited edge initial
      inheritedReady resident domain smaller stored active (below formulas solver budget rank) plan
  obtain ⟨_lawInventory, _lawPost, _resident, law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver reads
    inventory checks initial inheritedReady resident
  exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.descendants_complete actual,
    actual, reads, checks, post, residentAfter, storedAfter, narrow,
    (SourceCurrentAllocatedPartialActiveFrames.descendants actual).activeExcept active, law⟩
end FiniteOrdinaryOuterRowsKernels
#print axioms FiniteOrdinaryOuterRowsKernels.constructed_rows
#check @FiniteOrdinaryOuterRowsKernels.constructed_rows
#print axioms FiniteOrdinaryOuterRowsKernels.constructed_descendants
#check @FiniteOrdinaryOuterRowsKernels.constructed_descendants
