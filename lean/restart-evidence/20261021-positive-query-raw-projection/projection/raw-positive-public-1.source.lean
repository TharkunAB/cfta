import MicroCFTA.SourceCurrentCappedProjectionPositivePosition
import MicroCFTA.SourceCurrentRequiredRawCorridor

/-!
# Positive positions through actual raw-corridor projections

Full corridors use the existing capped observer. Ordinary corridors follow
the same selected child in the actual projection and row-read spine.
-/
namespace MicroCFTA.SourceCurrentRawCorridorPositiveProjection
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def RowPositive (row : Row) : List Nat → Prop
  | [] => SourceMemoGate.plain row.entry.key.constraint = false
  | index :: path => ∃ child, row.children[index]? = some child ∧ PositiveAt child path

private theorem earlier_guards {before after : Heap} (growth : Grows before after)
    (guards : Guards after) : Guards before := by
  intro key entry body depth ordinary present
  exact guards key entry body depth ordinary (growth.nodeRecords key _ present)

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem full_positive {path : List Nat} {value before result after}
    (project : Project (path.map Int.ofNat) value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (selected : rows[position]? = some row)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (readerSemantic : SemanticReady reader) (later : Keeps after reader)
    (readerGuards : Guards reader) (bounded : ∃ depth, Cap Plain depth value)
    (residual : List Nat) (positive : RowPositive row residual) :
    PositiveAt value (path ++ residual) := by
  obtain ⟨depth, bounded⟩ := bounded
  cases residual with
  | nil =>
    simpa only [List.append_nil] using SourceCurrentCappedProjectionPositivePosition.root project read position row selected
      semantic costs available guards readerSemantic later readerGuards depth bounded positive
  | cons index path =>
    obtain ⟨child, chosen, rest⟩ := positive
    exact SourceCurrentCappedProjectionPositivePosition.child project read position row selected index child chosen rest
      semantic costs available guards readerSemantic later readerGuards depth bounded

private theorem corridor_positive (path : List Nat) :
    ∀ {value : Node} {before result after},
    (project : Project (path.map Int.ofNat) value before result after) →
    ∀ {reader rows readAfter}, (read : Read result reader rows readAfter) →
    ∀ (position : Nat) (row : Row), rows[position]? = some row →
    SemanticReady before → CostHeap before → Available before value → Guards before →
    SemanticReady reader → Keeps after reader → Guards reader →
    RawCorridor (path.map Int.ofNat) value →
    ∀ residual, RowPositive row residual → PositiveAt value (path ++ residual) := by
  induction path with
  | nil =>
    intro value before result after project reader rows readAfter read position row selected
      semantic costs available guards readerSemantic later readerGuards corridor residual positive
    cases corridor with
    | full _ _ bounded =>
      exact full_positive project read position row selected semantic costs available guards readerSemantic later
        readerGuards bounded residual positive
  | cons index path ih =>
    intro value before result after project reader rows readAfter read position row selected
      semantic costs available guards readerSemantic later readerGuards corridor residual positive
    cases corridor with
    | full _ _ bounded =>
      exact full_positive project read position row selected semantic costs available guards readerSemantic later
        readerGuards bounded residual positive
    | node entry sourceEdges depth free _ _ children =>
      have spine := SourceCurrentProjectionReadSpine.project project semantic costs available read position row selected
      cases spine with
      | @ordinary remaining signedIndex sourceEdges before projectedMiddle values allRows unionMiddle result after
          entry depth free projects reads built reader rows readAfter read position row selected canonical rawIndex raw
          operandIndex operand operandSelected earlierRows selectedRows laterRows readStart readFinish
          readPrefix operandRead readSuffix parts readIndex readSelected sourceIndex sourceRow child start finish
          sourceSelected childSelected projectPrefix call projectSuffix rest =>
        have edges := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
        have earlierProject := SourceEqualityProjectionCosts.rows_effects projectPrefix semantic costs
          (fun row member => edges row (List.mem_of_mem_take member))
        have projected := SourceEqualityProjectionCosts.rows_effects projects semantic costs edges
        have earlier := SourceEqualityProjectionCosts.readAll_effects readPrefix projected.2.1 projected.2.2.1
          (fun value member => projected.2.2.2 value (List.mem_of_mem_take member))
        have childAvailable := earlierProject.2.1.ready.semantic.1.normal.facts.cached.edges sourceRow.entry.key sourceRow
          (edge_grows before start earlierProject.1.growth sourceRow (edges sourceRow (List.mem_of_getElem? sourceSelected)))
          child (select_member childSelected)
        have called := SourceEqualityProjectionCosts.project_effects call earlierProject.2.1 earlierProject.2.2.1 childAvailable
        have suffix := SourceEqualityProjectionCosts.rows_effects projectSuffix called.2.1 called.2.2.1
          (fun row member => edge_grows before finish (grows_trans earlierProject.1.growth called.1.growth)
            row (edges row (List.mem_of_mem_drop member)))
        have joined := SourceEqualityProjectionCosts.union_effects (.node reads built)
          projected.2.1 projected.2.2.1 projected.2.2.2
        have finalGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain
          (.ordinary (entry := entry) (depth := depth) (free := free) projects (.node reads built))
          semantic costs available guards
        have middleGuards := earlier_guards joined.1.growth finalGuards
        have firstGuards := earlier_guards (grows_trans called.1.growth suffix.1.growth) middleGuards
        have readGuards := SourceCurrentConstrainedCapProjectionGuard.readAll Plain readPrefix projected.2.1
          projected.2.2.1 (fun value member => projected.2.2.2 value (List.mem_of_mem_take member)) middleGuards
        have childCorridor := children sourceRow (List.mem_of_getElem? sourceSelected) child childSelected
        have childPositive := ih call operandRead readIndex row readSelected earlierProject.2.1
          earlierProject.2.2.1 childAvailable firstGuards earlier.2.1 (suffix.1.trans earlier.1) readGuards
          childCorridor residual positive
        have chosen : sourceRow.children[index]? = some child := by
          simpa only [select, Int.ofNat_eq_natCast,
            ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)), Int.toNat_natCast]
            using childSelected
        exact PositiveAt.child sourceIndex index sourceRow child sourceSelected chosen childPositive
      | @recursive original before exposed middle result after signedIndex remaining recursive head body
          reader rows readAfter read position row rest => cases recursive

/-- The same selected nonplain read row retains its full original natural path. -/
theorem root {path : List Nat} {value before result after}
    (project : Project (path.map Int.ofNat) value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (selected : rows[position]? = some row)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (readerSemantic : SemanticReady reader) (later : Keeps after reader)
    (readerGuards : Guards reader) (corridor : RawCorridor (path.map Int.ofNat) value)
    (nonplain : SourceMemoGate.plain row.entry.key.constraint = false) : PositiveAt value path := by
  simpa only [List.append_nil] using corridor_positive path project read position row selected semantic costs available
    guards readerSemantic later readerGuards corridor [] nonplain

/-- The same selected row and ordered child retain every positive descendant path. -/
theorem child {path residual : List Nat} {value before result after}
    (project : Project (path.map Int.ofNat) value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (selected : rows[position]? = some row)
    (childIndex : Nat) (child : Node) (chosen : row.children[childIndex]? = some child)
    (positive : PositiveAt child residual)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (readerSemantic : SemanticReady reader) (later : Keeps after reader)
    (readerGuards : Guards reader) (corridor : RawCorridor (path.map Int.ofNat) value) :
    PositiveAt value (path ++ childIndex :: residual) :=
  corridor_positive path project read position row selected semantic costs available guards readerSemantic later
    readerGuards corridor (childIndex :: residual) ⟨child, chosen, positive⟩

end Actual
end MicroCFTA.SourceCurrentRawCorridorPositiveProjection

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentRawCorridorPositiveProjection.root
#print MicroCFTA.SourceCurrentRawCorridorPositiveProjection.root
#print axioms MicroCFTA.SourceCurrentRawCorridorPositiveProjection.root

#check @MicroCFTA.SourceCurrentRawCorridorPositiveProjection.child
#print MicroCFTA.SourceCurrentRawCorridorPositiveProjection.child
#print axioms MicroCFTA.SourceCurrentRawCorridorPositiveProjection.child
