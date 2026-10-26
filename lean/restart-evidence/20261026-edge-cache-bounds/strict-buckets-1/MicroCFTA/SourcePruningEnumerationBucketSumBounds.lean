import MicroCFTA.SourcePruningEnumerationCostBounds

/-!
# Original sums of actual child buckets

Descent can only remove suspended entries. Each original child bucket
therefore contributes at most the inherited length plus the own-class count.
The sum counts every child and every repeated suspended entry.
-/
namespace MicroCFTA.SourcePruningEnumerationCostBounds
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint

/-- A uniform bound on original buckets bounds their complete sum. -/
theorem bucket_sum_le (inputs : List (Node × List Suspended)) (bound : Nat)
    (bounded : ∀ input ∈ inputs, input.2.length ≤ bound) :
    (inputs.map (fun input => input.2.length)).sum ≤ inputs.length * bound := by
  induction inputs with
  | nil => simp
  | cons input rest ih =>
    have head := bounded input List.mem_cons_self
    have tail := ih (fun later member => bounded later (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Every actual edge child bucket is bounded by its original inherited and own counts. -/
theorem child_bucket_le (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (start : Nat) (tries : List EqualityTrie.Trie) :
    ∀ input ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries,
      input.2.length ≤ scs.length + tries.length := by
  intro input member
  obtain ⟨indexed, _member, same⟩ := List.mem_map.mp member
  cases same
  have inherited := descend_length_le indexed.2 scs
  have own := descend_length_le indexed.2 (suspendedVars start tries)
  rw [suspended_length] at own
  simp only [List.length_append]
  omega

/-- The complete original child sum counts at most one uniform bucket per child. -/
theorem children_bucket_sum_le (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (start : Nat) (tries : List EqualityTrie.Trie) :
    ((SourcePruningEnumerationEdgeInputs.children edge scs start tries).map
      (fun input => input.2.length)).sum ≤ edge.children.length * (scs.length + tries.length) := by
  have bound := bucket_sum_le (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
    (scs.length + tries.length) (child_bucket_le edge scs start tries)
  simpa only [SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using bound

end MicroCFTA.SourcePruningEnumerationCostBounds
