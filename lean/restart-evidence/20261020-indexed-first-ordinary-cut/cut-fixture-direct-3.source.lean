import MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut
import MicroCFTA.SourceCurrentIndexedLeafSourceRows
import MicroCFTA.SourceCurrentConstrainedCapSourceHistory

/-!
# Actual union and open Mu prefixes before an ordinary child cut

A closed raw Mu precedes an open raw Mu. The open body's ordered children
contain the same closed leaf twice. The selected last leaf has a nonzero
root offset. Its row differs from the first ordinary parent row.
-/
namespace MicroCFTA.IndexedFirstOrdinaryCutKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentIndexedFirstOrdinaryCut (Cut split)
open InternedStoredSubstitution (leaves)
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def leafSource : Syntax Nat Bool := .node [.mk 17 true []]
private def preludeSource : Syntax Nat Bool := .binder false (.node [.mk 19 true []])
private def bodySource : Syntax Nat Bool := .node [.mk 7 false [leafSource,.var 0,.var 1,leafSource]]
private def muSource : Syntax Nat Bool := .binder false bodySource
private def source : Syntax Nat Bool := .union [preludeSource,muSource]
private def inputs : List Node := [.reference .depth]
private def valueOf (result : Outcome Nat Bool Node) : Node :=
  match result with | .done value _ => value | .pending .. => .empty
private def preludeRun := build preludeSource inputs (empty : Heap)
private def prelude : Node := valueOf preludeRun
private def leafRun := build leafSource inputs preludeRun.state
private def leaf : Node := valueOf leafRun
private def muRun := build muSource inputs preludeRun.state
private def muValue : Node := valueOf muRun
private def muBody : Node := match muValue with | .mu _ body _ _ => body | _ => .empty
private def wholeRun := build source inputs (empty : Heap)
private def raw : Node := valueOf wholeRun
private def leafRow : Row := (InternedEdgeResidency.nodeEdges leaf)[0]?.getD
  (run (makeEdge 0 false []) (empty : Heap)).1
private def parentRow : Row := (InternedEdgeResidency.nodeEdges muBody)[0]?.getD
  (run (makeEdge 0 false []) (empty : Heap)).1

private theorem context : Context (empty : Heap) inputs :=
  (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).local
    .depth (InternedNestedProvenance.depth_available _)
private theorem prelude_done : build preludeSource inputs (empty : Heap) = .done prelude preludeRun.state := by cbv
private theorem leaf_done : build leafSource inputs preludeRun.state = .done leaf leafRun.state := by cbv
private theorem mu_done : build muSource inputs preludeRun.state = .done muValue muRun.state := by cbv
private theorem whole_done : build source inputs (empty : Heap) = .done raw wholeRun.state := by cbv
private theorem leaf_closed : leaf.free = [] := by cbv
private theorem mu_open : muValue.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem raw_open : raw.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem repeated_first : (leaves raw)[1]? = some leaf := by cbv
private theorem repeated_selected : (leaves raw)[4]? = some leaf := by cbv
private theorem inside : RowAt leaf leafRow := by
  cbv
  exact .node (index := 0) rfl
private theorem symbols : parentRow.entry.key.symbol = 7 ∧ leafRow.entry.key.symbol = 17 := by cbv

private theorem no_direct : ¬ RowAt raw leafRow := by
  intro part
  cbv at part
  cases part with
  | @union _ _ _ _ index value row selected nested =>
      cases index with
      | zero =>
          have same := Option.some.inj selected
          subst value
          cases nested with
          | mu body =>
              cases body with
              | @node _ _ _ _ index row found =>
                  cases index with
                  | zero => cases found
                  | succ index => simp at found
      | succ index =>
          cases index with
          | zero =>
              have same := Option.some.inj selected
              subst value
              cases nested with
              | mu body =>
                  cases body with
                  | @node _ _ _ _ index row found =>
                      cases index with
                      | zero => cases found
                      | succ index => simp at found
          | succ index => simp at selected

private theorem explicit_cut : Cut raw 4 leaf parentRow 3 leaf 0 := by
  cbv
  refine .union (memberIndex := 1) (memberLeafIndex := 3) (by cbv; intro impossible; cases impossible) rfl (by cbv) ?_
  refine .mu (by cbv; intro impossible; cases impossible) ?_
  exact .node (outputIndex := 0) (by cbv; intro impossible; cases impossible) rfl rfl (by cbv) (by cbv)

private theorem forced_cut : ∃ row childIndex child inner,
    Cut raw 4 leaf row childIndex child inner ∧
    SourceRow source inputs (empty : Heap) raw wholeRun.state row ∧
    RowAt raw row ∧ row.children[childIndex]? = some child ∧
    (leaves child)[inner]? = some leaf ∧ row ≠ leafRow := by
  rcases SourceCurrentIndexedLeafSourceRows.source_cases source inputs (empty : Heap) raw wholeRun.state
    context whole_done 4 leaf repeated_selected leafRow inside with
    ⟨direct,_⟩ | ⟨row,childIndex,child,inner,cut,sourceRow⟩
  · exact False.elim (no_direct direct)
  · refine ⟨row,childIndex,child,inner,cut,sourceRow,cut.facts.1,cut.facts.2.1,cut.facts.2.2,?_⟩
    intro same
    exact no_direct (same ▸ cut.facts.1)

private theorem closed_cut_impossible {value : Node} {index leaf row childIndex child inner}
    (closed : value.free = []) (cut : Cut value index leaf row childIndex child inner) : False := by
  cases cut with
  | node opened _ _ _ _ => exact opened closed
  | union opened _ _ _ => exact opened closed
  | mu opened _ => exact opened closed

private theorem closed_direct : RowAt leaf leafRow := by
  have found : (leaves leaf)[0]? = some leaf := by cbv
  rcases split leaf 0 leaf found leafRow inside with direct | ⟨row,index,child,inner,cut⟩
  · exact direct
  · exact False.elim (closed_cut_impossible leaf_closed cut)

private theorem checked_witness :
    Context (empty : Heap) inputs ∧
    build preludeSource inputs (empty : Heap) = .done prelude preludeRun.state ∧
    build leafSource inputs preludeRun.state = .done leaf leafRun.state ∧
    build muSource inputs preludeRun.state = .done muValue muRun.state ∧
    build source inputs (empty : Heap) = .done raw wholeRun.state ∧
    leaf.free = [] ∧ muValue.free ≠ [] ∧ raw.free ≠ [] ∧
    (leaves raw)[1]? = some leaf ∧ (leaves raw)[4]? = some leaf ∧
    RowAt leaf leafRow ∧ parentRow.entry.key.symbol = 7 ∧ leafRow.entry.key.symbol = 17 ∧
    ¬ RowAt raw leafRow ∧ Cut raw 4 leaf parentRow 3 leaf 0 ∧
    (RowAt raw parentRow ∧ parentRow.children[3]? = some leaf ∧ (leaves leaf)[0]? = some leaf) ∧
    (∃ row childIndex child inner, Cut raw 4 leaf row childIndex child inner ∧
      SourceRow source inputs (empty : Heap) raw wholeRun.state row ∧
      RowAt raw row ∧ row.children[childIndex]? = some child ∧
      (leaves child)[inner]? = some leaf ∧ row ≠ leafRow) ∧
    RowAt leaf leafRow := by
  exact ⟨context,prelude_done,leaf_done,mu_done,whole_done,leaf_closed,mu_open,raw_open,
    repeated_first,repeated_selected,inside,symbols.1,symbols.2,no_direct,explicit_cut,
    explicit_cut.facts,forced_cut,closed_direct⟩

/-- Actual repeated leaves force a union/Mu-prefixed ordinary cut and preserve a separate closed-root case. -/
theorem actual_prefixes :
    Context (empty : Heap) inputs ∧
    build preludeSource inputs (empty : Heap) = .done prelude preludeRun.state ∧
    build leafSource inputs preludeRun.state = .done leaf leafRun.state ∧
    build muSource inputs preludeRun.state = .done muValue muRun.state ∧
    build source inputs (empty : Heap) = .done raw wholeRun.state ∧
    leaf.free = [] ∧ muValue.free ≠ [] ∧ raw.free ≠ [] ∧
    (leaves raw)[1]? = some leaf ∧ (leaves raw)[4]? = some leaf ∧
    RowAt leaf leafRow ∧ parentRow.entry.key.symbol = 7 ∧ leafRow.entry.key.symbol = 17 ∧
    ¬ RowAt raw leafRow ∧ Cut raw 4 leaf parentRow 3 leaf 0 ∧
    (RowAt raw parentRow ∧ parentRow.children[3]? = some leaf ∧ (leaves leaf)[0]? = some leaf) ∧
    (∃ row childIndex child inner, Cut raw 4 leaf row childIndex child inner ∧
      SourceRow source inputs (empty : Heap) raw wholeRun.state row ∧
      RowAt raw row ∧ row.children[childIndex]? = some child ∧
      (leaves child)[inner]? = some leaf ∧ row ≠ leafRow) ∧
    RowAt leaf leafRow := checked_witness

end MicroCFTA.IndexedFirstOrdinaryCutKernels
