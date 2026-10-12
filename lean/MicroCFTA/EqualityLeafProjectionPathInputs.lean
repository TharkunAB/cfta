import MicroCFTA.EqualityRawLeafEmpty

/-!
# Original leaf endpoints behind actual physical path reads

Canonical parent rows retain original occurrence children. The proof derives
their exact complete child lists from closed finite construction, then
transports the original leaf-endpoint invariant to each selected child.
-/
namespace MicroCFTA.EqualityLeafProjectionPathInputs
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionSyntax (Tree Edge Path LeafAt LeavesAt ChildAt)
open EqualityLeafProjectionCompile (Tag)

/-- A physical value has an original occurrence whose selected endpoint is a leaf. -/
def Input [DecidableEq (EdgeKey Symbol Guard)] (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (path : Path) (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ tree, LeafAt path tree ∧ Represents leaf tree state value

/-- Original endpoint validity holds for every original alternative. -/
theorem leaves_member (index : Nat) (path : Path) (edges : List (Edge Mark Leaf))
    (valid : LeavesAt index path edges) (tag : Mark) (children : List (Tree Mark Leaf))
    (member : .mk tag children ∈ edges) : ChildAt index path children := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk actual original =>
          rcases List.mem_cons.mp member with same | tail
          · cases same; exact valid.1
          · exact ih valid.2 tail

/-- Every actual original edge has its exact represented occurrence child list. -/
theorem edge_input [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state)
    (values : List (EdgeValue Symbol Guard)) (represented : RepresentsEdges leaf edges state values)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ values) :
    ∃ tag children, .mk tag children ∈ edges ∧ RepresentsForest leaf children state edge.children := by
  induction edges generalizing values with
  | nil =>
      have empty : values = [] := (congrArg (fun result : List (EdgeValue Symbol Guard) × State Symbol Guard => result.1) represented).symm
      simp only [empty, List.not_mem_nil] at member
  | cons first rest ih =>
      cases first with
      | mk tag children =>
          obtain ⟨nodes, head, tail, rfl, childClosed, edgeClosed, restClosed⟩ :=
            edges_decompose leaf tag children rest state facts.coherent.valid values represented
          rcases List.mem_cons.mp member with same | later
          · subst edge
            have available := forest_available leaf leaves children state facts nodes childClosed
            have fields := edge_fields tag nodes state facts available head edgeClosed
            exact ⟨tag, children, by simp, fields.2.2.symm ▸ childClosed⟩
          · obtain ⟨originalTag, originalChildren, present, closed⟩ := ih tail restClosed later
            exact ⟨originalTag, originalChildren, by simp [present], closed⟩

/-- Actual ordered lookup selects a represented original leaf endpoint. -/
theorem child_input [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (valid : Valid state) (values : List (Value Symbol Guard))
    (represented : RepresentsForest leaf forest state values) (endpoints : ChildAt index path forest)
    (value : Value Symbol Guard) (selected : values[index]? = some value) : Input leaf path state value := by
  induction forest generalizing index values with
  | nil =>
      have empty : values = [] := (congrArg (fun result : List (Value Symbol Guard) × State Symbol Guard => result.1) represented).symm
      simp only [empty, List.getElem?_nil, reduceCtorEq] at selected
  | cons first rest ih =>
      obtain ⟨head, tail, rfl, headClosed, tailClosed⟩ := forest_decompose leaf first rest state valid values represented
      cases index with
      | zero =>
          have same : head = value := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
          exact ⟨first, endpoints, same ▸ headClosed⟩
      | succ index => exact ih index tail tailClosed endpoints (by simpa only [List.getElem?_cons_succ] using selected)

/-- Canonical node normalization cannot introduce a new selected endpoint. -/
theorem node_inputs [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (represented : Represents leaf (.node edges) state value) (endpoints : LeavesAt index path edges) :
    ∀ edge ∈ nodeEdges value, ∀ child, edge.children[index]? = some child → Input leaf path state child := by
  obtain ⟨rows, rowsClosed, nodeClosed⟩ := node_decompose leaf edges state facts.coherent.valid value represented
  have rowsFacts := compileEdges_available leaf leaves edges state facts
  rw [rowsClosed] at rowsFacts
  have physical := EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked
    (fun edge member => (rowsFacts.2 edge member).1)
  rw [nodeClosed] at physical
  intro edge member child selected
  rw [physical] at member
  have original := (EqualityLeafProjectionPhysical.normalized_member state facts.coherent rows
    (fun edge member => (rowsFacts.2 edge member).1) edge).mp member
  obtain ⟨tag, children, included, childClosed⟩ := edge_input leaf leaves edges state facts rows rowsClosed edge original.1
  exact child_input leaf children index path state facts.coherent.valid edge.children childClosed
    (leaves_member index path edges endpoints tag children included) child selected

/-- A represented endpoint remains represented in every later coherent cache. -/
theorem input_grows [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (path : Path)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    (value : Value Symbol Guard) (input : Input leaf path before value) : Input leaf path after value := by
  obtain ⟨tree, endpoint, represented⟩ := input
  exact ⟨tree, endpoint, EqualityLeafProjectionRepresentation.grows leaf tree before after valid growth value represented⟩

end MicroCFTA.EqualityLeafProjectionPathInputs
