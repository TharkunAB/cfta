import MicroCFTA.SourcePruningEnumerationNativeBranchResources

/-!
# Original length bounds for selected alternatives

Descent does not increase a suspended bucket. Own classes add at most their
projected count to each child. The alternative bound counts every selected
row occurrence. Membership alone does not bound the number of occurrences.
-/
namespace MicroCFTA.SourcePruningEnumerationCostBounds
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint

/-- Descending a suspended bucket can only remove entries. -/
theorem descend_length_le (index : Nat) (scs : List Suspended) :
    (descendScs index scs).length ≤ scs.length := by
  simp only [descendScs, EqualityTrie.descendScs]
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_map _ _))

/-- Own-class suspension retains exactly one entry per projected trie. -/
theorem suspended_length (start : Nat) (tries : List EqualityTrie.Trie) :
    (suspendedVars start tries).length = tries.length := by
  induction tries generalizing start with
  | nil => rfl
  | cons trie rest ih => simp only [suspendedVars, List.length_cons, ih]

/-- A uniform bucket bound pays every original child and its extra mixed step. -/
theorem traversal_cost_le (inputs : List (Node × List Suspended)) (bound : Nat)
    (bounded : ∀ input ∈ inputs, input.2.length ≤ bound) :
    SourcePruningEnumerationTraversalCompletion.cost inputs ≤ inputs.length * (bound + 1) := by
  revert bounded
  induction inputs with
  | nil =>
      intro _bounded
      simp only [SourcePruningEnumerationTraversalCompletion.cost, List.length_nil, Nat.zero_mul]
  | cons input rest ih =>
      intro bounded
      have first := bounded input List.mem_cons_self
      have later := ih (fun item member => bounded item (List.mem_cons_of_mem _ member))
      change input.2.length + 1 + SourcePruningEnumerationTraversalCompletion.cost rest ≤
        (rest.length + 1) * (bound + 1)
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The actual indexed child buckets use only inherited entries and own classes. -/
theorem selected_cost_le (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (start : Nat) (tries : List EqualityTrie.Trie) (own : Nat) (ownBound : tries.length ≤ own) :
    SourcePruningEnumerationSelectedEdge.cost edge scs start tries ≤
      edge.children.length * (scs.length + own + 1) := by
  have buckets : ∀ input ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries,
      input.2.length ≤ scs.length + own := by
    intro input member
    obtain ⟨indexed, _indexedMember, same⟩ := List.mem_map.mp member
    cases same
    have inherited := descend_length_le indexed.2 scs
    have added := descend_length_le indexed.2 (suspendedVars start tries)
    rw [suspended_length] at added
    simp only [List.length_append]
    omega
  have result := traversal_cost_le (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
    (scs.length + own) buckets
  simpa only [SourcePruningEnumerationSelectedEdge.cost, SourcePruningEnumerationEdgeInputs.children,
    List.length_map, List.length_zipIdx] using result

/-- Rejected arity and unsupported projection cost zero; supported rows use the same width bound. -/
theorem edge_cost_le (scs : List Suspended) (start : Nat) (edge : EdgeValue Symbol Constraint)
    (arity own : Nat) (childBound : edge.children.length ≤ arity)
    (ownBound : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      tries.length ≤ own) :
    SourcePruningEnumerationNativeBranchCompletion.edgeCost scs start edge ≤
      arity * (scs.length + own + 1) := by
  unfold SourcePruningEnumerationNativeBranchCompletion.edgeCost
  by_cases allowed : arityAllows edge.children.length scs = true
  · rw [ite_eq_left allowed]
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => exact Nat.zero_le _
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact Nat.le_trans (selected_cost_le edge scs start tries own (ownBound tries residual projected))
          (Nat.mul_le_mul_right (scs.length + own + 1) childBound)
  · rw [ite_eq_right allowed]
    exact Nat.zero_le _

/-- Original row, child and projection widths bound the exact duplicate-sensitive alternative cost. -/
theorem cost_le (scs : List Suspended) (start : Nat) (selectedEdges : List (EdgeValue Symbol Constraint))
    (rows arity own : Nat) (rowsBound : selectedEdges.length ≤ rows)
    (childBound : ∀ edge ∈ selectedEdges, edge.children.length ≤ arity)
    (ownBound : ∀ edge ∈ selectedEdges, ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      tries.length ≤ own) :
    SourcePruningEnumerationNativeBranchCompletion.cost scs start selectedEdges ≤
      rows * arity * (scs.length + own + 1) := by
  have exactLength : SourcePruningEnumerationNativeBranchCompletion.cost scs start selectedEdges ≤
      selectedEdges.length * arity * (scs.length + own + 1) := by
    clear rowsBound
    revert childBound ownBound
    induction selectedEdges with
    | nil =>
        intro _childBound _ownBound
        simp only [SourcePruningEnumerationNativeBranchCompletion.cost, List.length_nil, Nat.zero_mul]
    | cons edge rest ih =>
        intro childBound ownBound
        have first := edge_cost_le scs start edge arity own (childBound edge List.mem_cons_self)
          (ownBound edge List.mem_cons_self)
        have later := ih
          (fun chosen member => childBound chosen (List.mem_cons_of_mem _ member))
          (fun chosen member => ownBound chosen (List.mem_cons_of_mem _ member))
        change SourcePruningEnumerationNativeBranchCompletion.edgeCost scs start edge +
          SourcePruningEnumerationNativeBranchCompletion.cost scs start rest ≤
          (rest.length + 1) * arity * (scs.length + own + 1)
        rw [Nat.add_mul, Nat.one_mul, Nat.add_mul]
        omega
  exact Nat.le_trans exactLength
    (Nat.mul_le_mul_right (scs.length + own + 1) (Nat.mul_le_mul_right arity rowsBound))

end MicroCFTA.SourcePruningEnumerationCostBounds
