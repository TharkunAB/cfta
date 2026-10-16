import MicroCFTA.SourceCurrentAllocatedPartialForestLanguage

#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_unchanged
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_unchanged
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_empty
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_empty
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_union
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.node_union
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.rows_nil
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.rows_nil
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.rows_cons
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.rows_cons
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.RowsLaw.exact
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.RowsLaw.exact
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.descendants
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.descendants
#print axioms MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.ordinary
#check @MicroCFTA.SourceCurrentAllocatedPartialForestLanguage.ordinary

namespace MicroCFTA.PartialForestLanguageIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedGuardedLanguage
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialGraph (Rows EdgeCall Descendants Children prefixState)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialWalkLanguage (ChildrenLaw)
open SourceCurrentAllocatedPartialForestLanguage
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)

/-- Even inherited contradiction does not invalidate an unchanged union return. -/
theorem unchanged_union_contradiction (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) :
    NodeLaw F S ⟨.contradiction, .union entry members depth free⟩ (.union entry members depth free) :=
  node_union F S .contradiction entry members depth free

/-- An empty return satisfies the same law without a parent acceptance premise. -/
theorem unchanged_empty_contradiction : NodeLaw F S ⟨.contradiction, .empty⟩ .empty :=
  node_empty F S .contradiction

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Actual physical edge reconstruction supplies the final descendant language step. -/
theorem descendants_from_physical {budget : Nat} {inherited combined : EqValue}
    {edge : EdgeValue Symbol Guard} {values : List (Value Symbol Guard)} {before middle : Caller width}
    {prefixInventory : Inventory} (inventory : Inventory)
    (prefixReceipt : SourceCurrentAllocatedInheritedPrefix.Receipt F S prefixInventory
      edge.entry.key.constraint inherited before.checked combined)
    (children : Children budget combined edge.children (prefixState before edge inherited) values middle)
    (childrenLaw : ChildrenLaw F S children)
    (ready : Ready middle.checked) (admitted : At F S inventory middle.checked)
    (resident : InternedEdgeResidency.EdgeResident middle.checked.native.machine.heap edge)
    (available : InternedNestedProvenance.Values middle.checked.native.machine.heap values)
    (same : values.length = edge.children.length) :
    EdgeLaw F S ⟨inherited, edge⟩ (SourceCurrentAllocatedRawRebuild.edge edge values middle.checked).1 := by
  have rebuilt := SourceCurrentAllocatedRawRebuild.edge_verified F S inventory edge values middle.checked
    ready admitted resident available same
  exact descendants F S prefixReceipt children childrenLaw rebuilt

/-- The actual modifyNode constructor turns smaller row laws into the ordinary parent law. -/
theorem ordinary_from_physical {budget : Nat} {inherited : EqValue}
    {entry : Interned InternedBinderProtocol.NodeKey} {edges results : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} {before middle : Caller width}
    (inventory : Inventory) (rows : Rows budget inherited edges before results middle)
    (law : RowsLaw F S rows) (ready : Ready middle.checked) (admitted : At F S inventory middle.checked)
    (available : Available middle.checked.native.machine.heap (.node entry edges depth free))
    (resident : InternedNestedProvenance.Edges middle.checked.native.machine.heap results) :
    NodeLaw F S ⟨inherited, .node entry edges depth free⟩
      (SourceCurrentAllocatedRawRebuild.modify (.node entry edges depth free) edges results middle.checked).1 := by
  have rebuilt := SourceCurrentAllocatedRawRebuild.modify_verified F S inventory entry edges results depth free
    middle.checked ready admitted available resident
  exact ordinary F S rows law rebuilt

/-- Two actual rows retain source order and multiplicity through both descendant calls. -/
theorem two_rows {budget : Nat} {inherited : EqValue}
    {left leftNarrowed leftResult right rightNarrowed rightResult : EdgeValue Symbol Guard}
    {before first afterFirst second afterSecond : Caller width}
    (leftCall : EdgeCall budget ⟨inherited, left⟩ before leftNarrowed first)
    (leftChildren : Descendants budget inherited leftNarrowed first leftResult afterFirst)
    (rightCall : EdgeCall budget ⟨inherited, right⟩ afterFirst rightNarrowed second)
    (rightChildren : Descendants budget inherited rightNarrowed second rightResult afterSecond)
    (leftLaw : EdgeLaw F S ⟨inherited, left⟩ leftNarrowed)
    (leftChildLaw : EdgeLaw F S ⟨inherited, leftNarrowed⟩ leftResult)
    (rightLaw : EdgeLaw F S ⟨inherited, right⟩ rightNarrowed)
    (rightChildLaw : EdgeLaw F S ⟨inherited, rightNarrowed⟩ rightResult) :
    RowsLaw F S (Rows.cons leftCall leftChildren (Rows.cons rightCall rightChildren Rows.nil)) :=
  rows_cons F S leftCall leftChildren _ leftLaw leftChildLaw
    (rows_cons F S rightCall rightChildren _ rightLaw rightChildLaw
      (rows_nil F S budget inherited afterSecond))

#print axioms unchanged_union_contradiction
#check @unchanged_union_contradiction
#print axioms unchanged_empty_contradiction
#check @unchanged_empty_contradiction
#print axioms descendants_from_physical
#check @descendants_from_physical
#print axioms ordinary_from_physical
#check @ordinary_from_physical
#print axioms two_rows
#check @two_rows
end MicroCFTA.PartialForestLanguageIndependent
