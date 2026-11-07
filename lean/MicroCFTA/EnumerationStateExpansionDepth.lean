import MicroCFTA.EnumerationStateReferenceBounds

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateExpansionDepth

open EnumerationState EnumerationStateExpansionBounds

variable {Symbol Guard α : Type}

mutual
  /-- Internal depth certificate for ordinary node expansion. -/
  def NodeDepth (graph : Graph Symbol Guard) (depth node : Nat) : Prop :=
    match depth with
    | 0 => False
    | remaining + 1 =>
      match graph.node node with
      | .alternatives edges => ∀ edge ∈ edges, EdgeDepth graph remaining edge
      | _ => True
  termination_by depth
  decreasing_by all_goals omega

  /-- Internal depth certificate for every ordinary child expansion. -/
  def EdgeDepth (graph : Graph Symbol Guard) (depth : Nat) (edge : Edge Symbol Guard) : Prop :=
    match depth with
    | 0 => False
    | remaining + 1 => ∀ child ∈ edge.children.zipIdx, NodeDepth graph remaining child.1
  termination_by depth
  decreasing_by all_goals omega
end

private theorem totalCost_mono (values : List α) (left right : α → Nat)
    (bounded : ∀ value ∈ values, left value ≤ right value) :
    totalCost left values ≤ totalCost right values := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    change left first + totalCost left rest ≤ right first + totalCost right rest
    exact Nat.add_le_add (bounded first (by simp))
      (ih (fun value member => bounded value (by simp [member])))

private theorem maxCost_mono (values : List α) (left right : α → Nat)
    (bounded : ∀ value ∈ values, left value ≤ right value) :
    maxCost left values ≤ maxCost right values := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    change max (left first) (maxCost left rest) ≤ max (right first) (maxCost right rest)
    have headBound := bounded first (by simp)
    have tailBound := ih (fun value member => bounded value (by simp [member]))
    omega

private theorem totalCost_congr (values : List α) (left right : α → Nat)
    (equal : ∀ value ∈ values, left value = right value) :
    totalCost left values = totalCost right values := by
  apply Nat.le_antisymm
  · exact totalCost_mono values left right (fun value member => Nat.le_of_eq (equal value member))
  · exact totalCost_mono values right left (fun value member => Nat.le_of_eq (equal value member).symm)

private theorem maxCost_congr (values : List α) (left right : α → Nat)
    (equal : ∀ value ∈ values, left value = right value) :
    maxCost left values = maxCost right values := by
  apply Nat.le_antisymm
  · exact maxCost_mono values left right (fun value member => Nat.le_of_eq (equal value member))
  · exact maxCost_mono values right left (fun value member => Nat.le_of_eq (equal value member).symm)

private theorem budget_monotone (graph : Graph Symbol Guard) (lower upper : Nat)
    (larger : lower ≤ upper) :
    (∀ node, nodeAllocationBudget graph lower node ≤ nodeAllocationBudget graph upper node) ∧
    (∀ edge, edgeAllocationBudget graph lower edge ≤ edgeAllocationBudget graph upper edge) := by
  induction lower generalizing upper with
  | zero =>
    constructor
    · intro node
      simpa only [nodeAllocationBudget] using Nat.zero_le (nodeAllocationBudget graph upper node)
    · intro edge
      simpa only [edgeAllocationBudget] using Nat.zero_le (edgeAllocationBudget graph upper edge)
  | succ lower ih =>
    cases upper with
    | zero => omega
    | succ upper =>
      obtain ⟨nodes, edges⟩ := ih upper (by omega)
      constructor
      · intro node
        cases view : graph.node node <;>
          simp only [nodeAllocationBudget, view]
        case alternatives alternatives =>
          exact maxCost_mono alternatives _ _ (fun edge _ => edges edge)
        all_goals exact Nat.le_refl _
      · intro edge
        simp only [edgeAllocationBudget]
        exact Nat.add_le_add_left
          (totalCost_mono edge.children.zipIdx _ _ (fun child _ => nodes child.1)) _

/-- Increasing fuel cannot decrease the allocation budget. -/
theorem node_budget_mono (graph : Graph Symbol Guard) (lower upper node : Nat)
    (larger : lower ≤ upper) :
    nodeAllocationBudget graph lower node ≤ nodeAllocationBudget graph upper node :=
  (budget_monotone graph lower upper larger).1 node

/-- Increasing fuel cannot decrease the edge allocation budget. -/
theorem edge_budget_mono (graph : Graph Symbol Guard) (lower upper : Nat)
    (edge : Edge Symbol Guard) (larger : lower ≤ upper) :
    edgeAllocationBudget graph lower edge ≤ edgeAllocationBudget graph upper edge :=
  (budget_monotone graph lower upper larger).2 edge

private theorem budget_stable (graph : Graph Symbol Guard) (depth extra : Nat) :
    (∀ node, NodeDepth graph depth node →
      nodeAllocationBudget graph (depth + extra) node = nodeAllocationBudget graph depth node) ∧
    (∀ edge, EdgeDepth graph depth edge →
      edgeAllocationBudget graph (depth + extra) edge = edgeAllocationBudget graph depth edge) := by
  induction depth with
  | zero =>
    constructor
    · intro node certificate
      simp only [NodeDepth] at certificate
    · intro edge certificate
      simp only [EdgeDepth] at certificate
  | succ depth ih =>
    obtain ⟨nodes, edges⟩ := ih
    constructor
    · intro node certificate
      cases view : graph.node node <;>
        simp only [Nat.succ_add, nodeAllocationBudget, view]
      case alternatives alternatives =>
        have allEdges : ∀ edge ∈ alternatives, EdgeDepth graph depth edge := by
          simpa only [NodeDepth, view] using certificate
        exact maxCost_congr alternatives _ _ (fun edge member => edges edge (allEdges edge member))
      all_goals rfl
    · intro edge certificate
      simp only [Nat.succ_add, edgeAllocationBudget]
      apply congrArg (fun cost => edge.equalities.length + cost)
      apply totalCost_congr
      intro child member
      have allChildren : ∀ child ∈ edge.children.zipIdx, NodeDepth graph depth child.1 := by
        simpa only [EdgeDepth] using certificate
      exact nodes child.1 (allChildren child member)

/-- Fuel above an internally certified depth leaves the node budget unchanged. -/
theorem node_budget_stable (graph : Graph Symbol Guard) (depth extra node : Nat)
    (certificate : NodeDepth graph depth node) :
    nodeAllocationBudget graph (depth + extra) node = nodeAllocationBudget graph depth node :=
  (budget_stable graph depth extra).1 node certificate

/-- Fuel above an internally certified depth leaves the edge budget unchanged. -/
theorem edge_budget_stable (graph : Graph Symbol Guard) (depth extra : Nat)
    (edge : Edge Symbol Guard) (certificate : EdgeDepth graph depth edge) :
    edgeAllocationBudget graph (depth + extra) edge = edgeAllocationBudget graph depth edge :=
  (budget_stable graph depth extra).2 edge certificate

/-- An internal node depth bounds allocations at every fuel value. -/
theorem node_budget_le_depth (graph : Graph Symbol Guard) (depth fuel node : Nat)
    (certificate : NodeDepth graph depth node) :
    nodeAllocationBudget graph fuel node ≤ nodeAllocationBudget graph depth node := by
  by_cases lower : fuel ≤ depth
  · exact node_budget_mono graph fuel depth node lower
  · have same : depth + (fuel - depth) = fuel := by omega
    have stable := node_budget_stable graph depth (fuel - depth) node certificate
    rw [same] at stable
    exact Nat.le_of_eq stable

/-- An internal edge depth bounds allocations at every fuel value. -/
theorem edge_budget_le_depth (graph : Graph Symbol Guard) (depth fuel : Nat)
    (edge : Edge Symbol Guard) (certificate : EdgeDepth graph depth edge) :
    edgeAllocationBudget graph fuel edge ≤ edgeAllocationBudget graph depth edge := by
  by_cases lower : fuel ≤ depth
  · exact edge_budget_mono graph fuel depth edge lower
  · have same : depth + (fuel - depth) = fuel := by omega
    have stable := edge_budget_stable graph depth (fuel - depth) edge certificate
    rw [same] at stable
    exact Nat.le_of_eq stable

private theorem fragment_mono
    (held : EnumerationStateReferenceBounds.FragmentBelow lower fragment)
    (larger : lower ≤ upper) :
    EnumerationStateReferenceBounds.FragmentBelow upper fragment := by
  induction held with
  | hole key below => exact .hole key (Nat.lt_of_lt_of_le below larger)
  | node symbol children below ih => exact .node symbol children (fun child member => ih child member)

/-- Initial node reference caps do not depend on the action's fuel after depth is proved. -/
theorem initial_node_references_below_depth (graph : Graph Symbol Guard)
    (depth fuel root : Nat) (certificate : NodeDepth graph depth root)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph fuel [] root (EnumerationState.initial root))) :
    let cap := 1 + nodeAllocationBudget graph depth root
    EnumerationStateReferenceBounds.Invariant cap after ∧
      EnumerationStateReferenceBounds.FragmentBelow cap fragment := by
  obtain ⟨state, output⟩ :=
    EnumerationStateReferenceBounds.enumerateNode_initial_references graph fuel root fragment after returned
  have budget := node_budget_le_depth graph depth fuel root certificate
  exact ⟨EnumerationStateReferenceBounds.invariant_mono state (by omega),
    fragment_mono output (by omega)⟩

/-- Initial edge reference caps do not depend on the action's fuel after depth is proved. -/
theorem initial_edge_references_below_depth (graph : Graph Symbol Guard)
    (depth fuel root : Nat) (edge : Edge Symbol Guard) (certificate : EdgeDepth graph depth edge)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph fuel [] edge (EnumerationState.initial root))) :
    let cap := 1 + edgeAllocationBudget graph depth edge
    EnumerationStateReferenceBounds.Invariant cap after ∧
      EnumerationStateReferenceBounds.FragmentBelow cap fragment := by
  obtain ⟨state, output⟩ :=
    EnumerationStateReferenceBounds.enumerateEdge_initial_references graph fuel root edge fragment after returned
  have budget := edge_budget_le_depth graph depth fuel edge certificate
  exact ⟨EnumerationStateReferenceBounds.invariant_mono state (by omega),
    fragment_mono output (by omega)⟩

/-- The abstract interface can repeat an ordinary child and allocate on each visit. -/
def ordinaryCycleGraph (base : Graph Symbol Guard) (edge : Edge Symbol Guard)
    (trie : EqualityTrie.Trie) (node : Nat) : Graph Symbol Guard :=
  { base with node := fun _ => .alternatives [{ edge with children := [node], equalities := [trie] }] }

/-- An ordinary interface cycle has an unbounded allocation budget as fuel increases. -/
theorem ordinary_cycle_budget (base : Graph Symbol Guard) (edge : Edge Symbol Guard)
    (trie : EqualityTrie.Trie) (node count : Nat) :
    nodeAllocationBudget (ordinaryCycleGraph base edge trie node) (2 * count + 1) node = count := by
  induction count with
  | zero =>
    simp [ordinaryCycleGraph, nodeAllocationBudget, edgeAllocationBudget, maxCost]
  | succ count ih =>
    have step : 2 * (count + 1) + 1 = ((2 * count + 1) + 1) + 1 := by omega
    rw [step]
    simp [ordinaryCycleGraph, nodeAllocationBudget, edgeAllocationBudget, maxCost, totalCost] at ih ⊢
    omega

/-- A finite ordinary interface cycle need not have a uniform allocation-budget bound. -/
theorem ordinary_cycle_no_uniform_budget (base : Graph Symbol Guard) (edge : Edge Symbol Guard)
    (trie : EqualityTrie.Trie) (node : Nat) :
    ¬ ∃ bound, ∀ fuel,
      nodeAllocationBudget (ordinaryCycleGraph base edge trie node) fuel node ≤ bound := by
  rintro ⟨bound, bounded⟩
  have tooLarge := bounded (2 * (bound + 1) + 1)
  rw [ordinary_cycle_budget] at tooLarge
  omega

/-- The interface cycle has no ordinary depth certificate at any depth. -/
theorem ordinary_cycle_no_depth (base : Graph Symbol Guard) (edge : Edge Symbol Guard)
    (trie : EqualityTrie.Trie) (node depth : Nat) :
    ¬ NodeDepth (ordinaryCycleGraph base edge trie node) depth node := by
  intro certificate
  apply ordinary_cycle_no_uniform_budget base edge trie node
  exact ⟨nodeAllocationBudget _ depth node, fun fuel => node_budget_le_depth _ depth fuel node certificate⟩

end MicroCFTA.EnumerationStateExpansionDepth
