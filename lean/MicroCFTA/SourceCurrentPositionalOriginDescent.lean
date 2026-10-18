import MicroCFTA.SourceCurrentActualRequiredRowOrigins
import MicroCFTA.InternedValueMass

/-!
# Strict continuation descent from an immediate row-origin anchor

A positive row with an unchanged continuation retains an indexed source
row. That continuation has smaller mass than the explicit source anchor.
The anchor can be a reconstructed value. This theorem does not identify
an occurrence in the initial source or a decreasing outer recursion rank.
-/
namespace MicroCFTA.SourceCurrentPositionalOriginDescent
open InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentActualRequiredRowOrigins (Link)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- A positive retained continuation is a strict child of its explicit immediate source anchor. -/
theorem continuation {childIndex : Nat} {anchor result : Node} (link : Link childIndex anchor result)
    {row : Edge} (member : row ∈ nodeEdges result) {records : List SourceEqualityClassOrder.Record}
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) {child : Node} (present : row.children[childIndex]? = some child) :
    ∃ (sourceIndex : Nat) (original : Edge), (nodeEdges anchor)[sourceIndex]? = some original ∧
      RowOrigin original row ∧ row.children[childIndex]? = original.children[childIndex]? ∧
      original.children[childIndex]? = some child ∧
      InternedValueMass.value child < InternedValueMass.value anchor := by
  obtain ⟨sourceIndex,original,found,origin,unchanged⟩ := link.positive member positive nonempty
  have originalPresent : original.children[childIndex]? = some child := unchanged.symm.trans present
  refine ⟨sourceIndex,original,found,origin,unchanged,originalPresent,?_⟩
  cases anchor with
  | empty | reference | union | mu => cases found
  | node entry rows level free =>
    exact InternedValueMass.node_child_lt entry rows level free original
      (List.mem_of_getElem? found) child (List.mem_of_getElem? originalPresent)

end MicroCFTA.SourceCurrentPositionalOriginDescent
