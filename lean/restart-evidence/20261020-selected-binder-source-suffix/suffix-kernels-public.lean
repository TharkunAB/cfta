import MicroCFTA.SourceCurrentSourceRowTerminalSuffix

/-!
# Actual terminal source suffix through two unions

The original node has two equal children. Two later source members allocate
rows after that node returns. The terminal certificate comes from the actual
whole source call. Its existential terminal return is not identified with the
separately computed node return.
-/
namespace MicroCFTA.TerminalSourceSuffixFixture
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinarySourceHistory (Reached reached_initial)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow build_row_origin)
open SourceCurrentSourceRowTerminalSuffix (terminal_source)
open InternedEdgeResidency (nodeEdges)
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def leafSource : Syntax Nat Bool := .node [.mk 17 true []]
private def nodeSource : Syntax Nat Bool := .node [.mk 5 false [leafSource,leafSource]]
private def innerSource : Syntax Nat Bool := .union [nodeSource,.node [.mk 99 true []]]
private def source : Syntax Nat Bool := .union [innerSource,.node [.mk 100 false []]]
private def valueOf (outcome : Outcome Nat Bool Node) : Node :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def nodeRun := build nodeSource [] (empty : Heap)
private def node : Node := valueOf nodeRun
private def wholeRun := build source [] (empty : Heap)
private def raw : Node := valueOf wholeRun
private def parentRow : Row := (nodeEdges node)[0]?.getD
  (run (makeEdge 0 false []) (empty : Heap)).1
private theorem context : Context (empty : Heap) [] :=
  SourceCurrentConstrainedCapSourceHistory.empty_context
private theorem node_done : build nodeSource [] (empty : Heap) = .done node nodeRun.state := by cbv
private theorem whole_done : build source [] (empty : Heap) = .done raw wholeRun.state := by cbv
private theorem different_returns : nodeRun.state ≠ wholeRun.state := by
  intro same
  have counts := congrArg (fun state : Heap => state.nodes.next) same
  cbv at counts
private theorem actual_row : RowAt raw parentRow := by
  cbv
  exact .node (index := 0) rfl
private theorem source_row : SourceRow source [] (empty : Heap) raw wholeRun.state parentRow :=
  build_row_origin source [] (empty : Heap) raw wholeRun.state context whole_done parentRow actual_row
private theorem initial_reached : Reached source [] source [] (empty : Heap) :=
  reached_initial source [] (empty : Heap)

private theorem checked_witness :
    Context (empty : Heap) [] ∧
    Reached source [] source [] (empty : Heap) ∧
    build nodeSource [] (empty : Heap) = .done node nodeRun.state ∧
    build source [] (empty : Heap) = .done raw wholeRun.state ∧
    nodeRun.state ≠ wholeRun.state ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    parentRow.children.length = 2 ∧ parentRow.children[0]? = parentRow.children[1]? ∧
    RowAt raw parentRow ∧
    SourceRow source [] (empty : Heap) raw wholeRun.state parentRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter parentRow ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached source [] terminalExpression terminalInputs terminalBefore ∧
      @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) terminalExpression ≤
        @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) source ∧
      Grows terminalAfter wholeRun.state ∧
      Extends terminalAfter.nodes.issued wholeRun.state.nodes.issued := by
  refine ⟨context,initial_reached,node_done,whole_done,different_returns,?_,?_,?_,?_,actual_row,source_row,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · exact terminal_source context initial_reached source_row

/-- The actual selected row retains its terminal call and whole-return suffix across two source unions. -/
theorem actual_two_union_suffix :
    Context (empty : Heap) [] ∧
    Reached source [] source [] (empty : Heap) ∧
    build nodeSource [] (empty : Heap) = .done node nodeRun.state ∧
    build source [] (empty : Heap) = .done raw wholeRun.state ∧
    nodeRun.state ≠ wholeRun.state ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    parentRow.children.length = 2 ∧ parentRow.children[0]? = parentRow.children[1]? ∧
    RowAt raw parentRow ∧
    SourceRow source [] (empty : Heap) raw wholeRun.state parentRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter parentRow ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached source [] terminalExpression terminalInputs terminalBefore ∧
      @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) terminalExpression ≤
        @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) source ∧
      Grows terminalAfter wholeRun.state ∧
      Extends terminalAfter.nodes.issued wholeRun.state.nodes.issued := checked_witness

end MicroCFTA.TerminalSourceSuffixFixture

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.TerminalSourceSuffixFixture.actual_two_union_suffix
#print MicroCFTA.TerminalSourceSuffixFixture.actual_two_union_suffix
#print axioms MicroCFTA.TerminalSourceSuffixFixture.actual_two_union_suffix
