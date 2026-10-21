import MicroCFTA.SourceCurrentCappedProjectionPositivePosition

/-!
# Positive positions through actual capped Head exposure

The actual read supplies the original rows. Node construction can remove
rows. Each returned positive row retains its exact original read row and
ordered child index.
-/
namespace MicroCFTA.SourceCurrentCappedHeadPositivePosition
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead
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

/-- An actual capped Head return retains every positive path in its input. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Node} {before after : Heap}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (depth : Nat) (bounded : Cap Plain depth value)
    {path : List Nat} (positive : PositiveAt result path) : PositiveAt value path := by
  cases actual with
  | read fuel rows middle exposed built =>
    have read : Read value before rows middle := .done fuel exposed
    have effects := SourceEqualityProjectionCosts.read_effects read semantic costs available
    have fields := EqualityLeafProjectionPhysical.makeNode_edges rows middle
      effects.2.1.ready.semantic.1.normal.facts.coherent
      effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2
    have ordinary : Ordinary result := by
      simpa only [built] using SourceEqualityRequiredCache.node_ordinary rows middle
        effects.2.1.ready.semantic.1.normal.facts effects.2.2.2
    have raw : ∀ row ∈ nodeEdges result, row ∈ rows := by
      intro row member
      rw [built] at fields
      exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
    cases positive with
    | root position row selected nonplain =>
      obtain ⟨readIndex,readSelected⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact SourceCurrentCappedProjectionPositivePosition.root (path := []) Project.root read
        readIndex row readSelected semantic costs available guards semantic
        (pure_keeps before semantic.ready) guards depth bounded nonplain
    | child position childIndex row child selected chosen rest =>
      obtain ⟨readIndex,readSelected⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact SourceCurrentCappedProjectionPositivePosition.child (path := []) Project.root read
        readIndex row readSelected childIndex child chosen rest semantic costs available guards semantic
        (pure_keeps before semantic.ready) guards depth bounded
    | member => cases ordinary

end MicroCFTA.SourceCurrentCappedHeadPositivePosition

set_option linter.all true
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentCappedHeadPositivePosition.head
#print MicroCFTA.SourceCurrentCappedHeadPositivePosition.head
#print axioms MicroCFTA.SourceCurrentCappedHeadPositivePosition.head
