import MicroCFTA.SourceCurrentRootedRowChildOrigins

/-!
# A closed original source node inside an open union

The actual whole build supplies its source-row receipt. The rooted child
producer selects the second of two equal children. Its node receipt is
extracted from that returned Origin. No parallel Origin is constructed.
-/
namespace MicroCFTA.RootedIndexedSourceChildFixture
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedFreshOrdinarySourceHistory (Reached reached_initial)
open InternedFreshOrdinaryActiveOrigins (Path)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow build_row_origin)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentRootedRowChildOrigins (Origin from_source_row)
open InternedEdgeResidency (nodeEdges)
open InternedStoredSubstitution (leaves)
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def leafSource : Syntax Nat Bool := .node [.mk 17 true []]
private def nodeSource : Syntax Nat Bool := .node [.mk 5 false [leafSource,leafSource]]
private def source : Syntax Nat Bool := .union [nodeSource,.var 0]
private def inputs : List Node := [.reference .depth]
private def valueOf (outcome : Outcome Nat Bool Node) : Node :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leafRun := build leafSource inputs (empty : Heap)
private def leaf : Node := valueOf leafRun
private def nodeRun := build nodeSource inputs (empty : Heap)
private def node : Node := valueOf nodeRun
private def wholeRun := build source inputs (empty : Heap)
private def raw : Node := valueOf wholeRun
private def parentRow : Row := (nodeEdges node)[0]?.getD
  (run (makeEdge 0 false []) (empty : Heap)).1

private theorem context : Context (empty : Heap) inputs :=
  (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).local
    .depth (InternedNestedProvenance.depth_available _)
private theorem node_done : build nodeSource inputs (empty : Heap) = .done node nodeRun.state := by cbv
private theorem whole_done : build source inputs (empty : Heap) = .done raw wholeRun.state := by cbv
private theorem node_closed : node.free = [] := by cbv
private theorem raw_open : raw.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem child_zero : parentRow.children[0]? = some leaf := by cbv
private theorem child_one : parentRow.children[1]? = some leaf := by cbv
private theorem row_fields : parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false := by cbv
private theorem actual_row : RowAt raw parentRow := by
  cbv
  exact .union (index := 0) rfl (.node (index := 0) rfl)
private theorem source_row : SourceRow source inputs (empty : Heap) raw wholeRun.state parentRow :=
  build_row_origin source inputs (empty : Heap) raw wholeRun.state context whole_done parentRow actual_row
private theorem initial_reached : Reached source inputs source inputs (empty : Heap) :=
  reached_initial source inputs (empty : Heap)
private theorem origin : Origin source inputs source parentRow 1 leaf :=
  from_source_row context initial_reached source_row 1 leaf child_one

private theorem leaf_path {target : Syntax Nat Bool} {environment crossings}
    (path : Path leafSource inputs target environment crossings) :
    environment = inputs ∧ target = leafSource := by
  cases path with
  | here => exact ⟨rfl,rfl⟩
  | node edge member nested =>
      have same := List.mem_singleton.mp edge
      cases same
      cases member

private theorem node_path {target : Syntax Nat Bool} {environment crossings}
    (path : Path nodeSource inputs target environment crossings) :
    environment = inputs ∧ (target = nodeSource ∨ target = leafSource) := by
  cases path with
  | here => exact ⟨rfl,.inl rfl⟩
  | @node edges symbol guard children child target environment current crossings edge member nested =>
      have same := List.mem_singleton.mp edge
      cases same
      have childSame : child = leafSource := by simpa only [List.mem_cons,List.mem_nil_iff,or_false,or_self] using member
      subst childSame
      have result := leaf_path nested
      exact ⟨result.1,.inr result.2⟩

private theorem root_path {target : Syntax Nat Bool} {environment crossings}
    (path : Path source inputs target environment crossings) :
    environment = inputs ∧
      (target = source ∨ target = nodeSource ∨ target = leafSource ∨ target = .var 0) := by
  cases path with
  | here => exact ⟨rfl,.inl rfl⟩
  | @union members child target environment current crossings member nested =>
      have alternatives : child = nodeSource ∨ child = (Syntax.var 0 : Syntax Nat Bool) := by
        simpa only [List.mem_cons,List.mem_nil_iff,or_false] using member
      rcases alternatives with same | same
      · subst same
        have result := node_path nested
        rcases result.2 with same | same
        · exact ⟨result.1,.inr (.inl same)⟩
        · exact ⟨result.1,.inr (.inr (.inl same))⟩
      · subst same
        cases nested with
        | here => exact ⟨rfl,.inr (.inr (.inr rfl))⟩

private def NodeReceipt : Prop :=
  ∃ expressions captures before value after rows middle symbol guard children (sourceIndex outputIndex : Nat),
    ∃ call : RowCall expressions captures before rows middle after sourceIndex symbol guard children,
    ∃ childSyntax current next,
      buildEdges expressions captures before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) ∧
      (nodeEdges value)[outputIndex]? = some parentRow ∧ call.output = parentRow ∧
      children[1]? = some childSyntax ∧ call.values[1]? = some leaf ∧
      buildMany (children.take 1) captures call.current = .done (call.values.take 1) current ∧
      Context current captures ∧ build childSyntax captures current = .done leaf next ∧
      buildMany (children.drop 2) captures next = .done (call.values.drop 2) call.middle ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Reached source inputs childSyntax captures current ∧
      @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) childSyntax <
        @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) source

private theorem node_receipt : NodeReceipt := by
  cases origin with
  | @node expressions captures before value after rows middle symbol guard children sourceIndex outputIndex
      built made canonical call same childSyntax current next syntaxSelected valueSelected earlier
      childContext called suffix growth issued reached smaller =>
      exact ⟨expressions,captures,before,value,after,rows,middle,symbol,guard,children,sourceIndex,outputIndex,
        call,childSyntax,current,next,built,made,canonical,same,syntaxSelected,valueSelected,earlier,
        childContext,called,suffix,growth,issued,reached,smaller⟩
  | @capture captures state value slot selected inside _ reached =>
      obtain ⟨crossings,path,_⟩ := reached
      have capturesSame := (root_path path).1
      subst captures
      cases slot with
      | zero =>
          have same : Value.reference .depth = value := Option.some.inj selected
          subst value
          cases inside
      | succ slot => simp only [inputs,List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  | @binder smart expression captures before value after depth afterDepth ordinary cut entry body
      _ _ _ _ _ _ _ reached =>
      obtain ⟨crossings,path,_⟩ := reached
      rcases (root_path path).2 with same | same | same | same <;> cases same

private theorem checked_witness :
    Context (empty : Heap) inputs ∧ Reached source inputs source inputs (empty : Heap) ∧
    build nodeSource inputs (empty : Heap) = .done node nodeRun.state ∧
    build source inputs (empty : Heap) = .done raw wholeRun.state ∧
    node.free = [] ∧ raw.free ≠ [] ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    parentRow.children[0]? = some leaf ∧ parentRow.children[1]? = some leaf ∧ (0 : Nat) ≠ 1 ∧
    RowAt raw parentRow ∧ SourceRow source inputs (empty : Heap) raw wholeRun.state parentRow ∧
    Origin source inputs source parentRow 1 leaf ∧ NodeReceipt := by
  exact ⟨context,initial_reached,node_done,whole_done,node_closed,raw_open,row_fields.1,row_fields.2,
    child_zero,child_one,by decide,actual_row,source_row,origin,node_receipt⟩

/-- A closed original node inside an open actual union supplies the second equal child's rooted call. -/
theorem actual_closed_member :
    Context (empty : Heap) inputs ∧ Reached source inputs source inputs (empty : Heap) ∧
    build nodeSource inputs (empty : Heap) = .done node nodeRun.state ∧
    build source inputs (empty : Heap) = .done raw wholeRun.state ∧
    node.free = [] ∧ raw.free ≠ [] ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    parentRow.children[0]? = some leaf ∧ parentRow.children[1]? = some leaf ∧ (0 : Nat) ≠ 1 ∧
    RowAt raw parentRow ∧ SourceRow source inputs (empty : Heap) raw wholeRun.state parentRow ∧
    Origin source inputs source parentRow 1 leaf ∧
  ∃ expressions captures before value after rows middle symbol guard children (sourceIndex outputIndex : Nat),
    ∃ call : RowCall expressions captures before rows middle after sourceIndex symbol guard children,
    ∃ childSyntax current next,
      buildEdges expressions captures before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) ∧
      (nodeEdges value)[outputIndex]? = some parentRow ∧ call.output = parentRow ∧
      children[1]? = some childSyntax ∧ call.values[1]? = some leaf ∧
      buildMany (children.take 1) captures call.current = .done (call.values.take 1) current ∧
      Context current captures ∧ build childSyntax captures current = .done leaf next ∧
      buildMany (children.drop 2) captures next = .done (call.values.drop 2) call.middle ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Reached source inputs childSyntax captures current ∧
      @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) childSyntax <
        @sizeOf (Syntax Nat Bool) (@Syntax._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) source := checked_witness

end MicroCFTA.RootedIndexedSourceChildFixture
