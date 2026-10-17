import MicroCFTA.InternedValueMass
import MicroCFTA.InternedFreshOrdinaryStoredAllocationBudget

/-!
# Initial structural mass bounds full stored encoding allocation

The complete encoder can reconstruct open nested Mu and stored unions.
Its full fresh-schedule budgets are bounded by a power of structural mass.
The bound uses no key, metadata, context length, or replacement-size limit.
It bounds local substitution and unfolding. Whole-query initial resources
require a separate bound on each generated input value.
-/
namespace MicroCFTA.InternedStoredEncodingMass
open InternedConstructorTemplates
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment leaves encode encodeMany encodeEdges)
open InternedFreshOrdinaryAllocationBudget (nodeBudget edgeBudget manyNodes manyEdges rowNodes rowEdges)
local notation "Mass" => InternedValueMass.value
variable {Symbol Guard : Type}

private theorem potential_mono {first last : Nat} (increase : first ≤ last) :
    2 * 3 ^ first ≤ 2 * 3 ^ last :=
  Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) increase)

private theorem potential_zero (mass : Nat) : 2 ≤ 2 * 3 ^ mass := by
  simpa only [Nat.pow_zero, Nat.mul_one] using potential_mono (first := 0) (Nat.zero_le mass)

private theorem add_layer {cost mass : Nat} (bound : cost + 2 ≤ 2 * 3 ^ mass) :
    cost + 3 ≤ 2 * 3 ^ (1 + mass) := by
  rw [Nat.add_comm 1 mass, Nat.pow_succ]
  omega

private theorem triple_layer {cost mass : Nat} (bound : cost + 2 ≤ 2 * 3 ^ mass) :
    3 * cost + 6 ≤ 2 * 3 ^ (1 + mass) := by
  rw [Nat.add_comm 1 mass, Nat.pow_succ]
  omega

private theorem sum_layer {first last left right : Nat}
    (firstBound : first + 2 ≤ 2 * 3 ^ left) (lastBound : last + 2 ≤ 2 * 3 ^ right) :
    first + last + 3 ≤ 2 * 3 ^ (1 + left + right) := by
  have firstLarge := Nat.le_trans firstBound (potential_mono (show left ≤ left + right by omega))
  have lastLarge := Nat.le_trans lastBound (potential_mono (show right ≤ left + right by omega))
  rw [show 1 + left + right = (left + right) + 1 by omega, Nat.pow_succ]
  omega

mutual
/-- Any lexical encoding has full node and edge budgets bounded by the initial complete value mass. -/
theorem encode_bound (context : List (Value Symbol Guard)) (locals : List Reference) (node : Value Symbol Guard) :
    nodeBudget (encode context locals node) + 2 ≤ 2 * 3 ^ Mass node ∧
      edgeBudget (encode context locals node) + 2 ≤ 2 * 3 ^ Mass node := by
  rw [encode.eq_def]
  split
  · simp only [nodeBudget, edgeBudget]
    exact ⟨potential_zero _, potential_zero _⟩
  · cases node with
    | empty => simp only [nodeBudget, edgeBudget, InternedValueMass.value]; omega
    | reference name =>
        cases found : locals.findIdx? (· == name) <;>
          simp only [found, nodeBudget, edgeBudget, InternedValueMass.value] <;> omega
    | node entry rows level free =>
        have bounded := encodeEdges_bound context locals rows
        have nodes := add_layer bounded.1
        have edges := Nat.le_trans bounded.2 (potential_mono (show InternedValueMass.edges rows ≤ 1 + InternedValueMass.edges rows by omega))
        simpa only [nodeBudget, edgeBudget, InternedValueMass.value, Nat.add_assoc] using And.intro nodes edges
    | union entry members level free =>
        have bounded := encodeMany_bound context locals members
        have nodes := add_layer bounded.1
        have edges := Nat.le_trans bounded.2 (potential_mono (show InternedValueMass.values members ≤ 1 + InternedValueMass.values members by omega))
        simpa only [nodeBudget, edgeBudget, InternedValueMass.value, Nat.add_assoc] using And.intro nodes edges
    | mu entry body depth ordinary =>
        have bounded := encode_bound context (.interned entry.identity :: locals) body
        have growth := potential_mono (show 1 + Mass body ≤ 1 + Mass body + Mass depth + Mass ordinary by omega)
        have nodes := Nat.le_trans (triple_layer bounded.1) growth
        have edges := Nat.le_trans (triple_layer bounded.2) growth
        simp only [nodeBudget, edgeBudget, InternedValueMass.value]
        constructor <;> omega
termination_by sizeOf node

/-- Ordered encoded values retain a bound from the original complete list mass. -/
theorem encodeMany_bound (context : List (Value Symbol Guard)) (locals : List Reference)
    (nodes : List (Value Symbol Guard)) :
    manyNodes (encodeMany context locals nodes) + 2 ≤ 2 * 3 ^ InternedValueMass.values nodes ∧
      manyEdges (encodeMany context locals nodes) + 2 ≤ 2 * 3 ^ InternedValueMass.values nodes := by
  cases nodes with
  | nil => simp only [encodeMany, manyNodes, manyEdges, InternedValueMass.values]; omega
  | cons first rest =>
      have firstBound := encode_bound context locals first
      have lastBound := encodeMany_bound context locals rest
      have nodes := sum_layer firstBound.1 lastBound.1
      have edges := sum_layer firstBound.2 lastBound.2
      simp only [encodeMany, manyNodes, manyEdges, InternedValueMass.values]
      constructor <;> omega
termination_by sizeOf nodes

/-- Ordered encoded edges retain a bound from the original complete row-list mass. -/
theorem encodeEdges_bound (context : List (Value Symbol Guard)) (locals : List Reference)
    (rows : List (EdgeValue Symbol Guard)) :
    rowNodes (encodeEdges context locals rows) + 2 ≤ 2 * 3 ^ InternedValueMass.edges rows ∧
      rowEdges (encodeEdges context locals rows) + 2 ≤ 2 * 3 ^ InternedValueMass.edges rows := by
  cases rows with
  | nil => simp only [encodeEdges, rowNodes, rowEdges, InternedValueMass.edges]; omega
  | cons first rest =>
      cases first with
      | mk entry children =>
          have childBound := encodeMany_bound context locals children
          have lastBound := encodeEdges_bound context locals rest
          have growth := potential_mono (show 1 + InternedValueMass.values children + InternedValueMass.edges rest ≤
              1 + (1 + InternedValueMass.values children) + InternedValueMass.edges rest by omega)
          have nodes := Nat.le_trans (sum_layer childBound.1 lastBound.1) growth
          have edges := Nat.le_trans (sum_layer childBound.2 lastBound.2) growth
          simp only [encodeEdges, rowNodes, rowEdges, InternedValueMass.edges, InternedValueMass.edge]
          constructor <;> omega
termination_by sizeOf rows
end

/-- Actual repaired substitution charges depend only on the complete initial value mass. -/
theorem execute_charges (node : Value Symbol Guard) :
    (InternedFreshOrdinaryStoredAllocationBudget.executeCharges node).1 + 2 ≤ 2 * 3 ^ Mass node ∧
      (InternedFreshOrdinaryStoredAllocationBudget.executeCharges node).2 + 2 ≤ 2 * 3 ^ Mass node :=
  encode_bound (leaves node) [] node

/-- Actual unfolding charges depend only on the complete initial recursive value mass. -/
theorem unfold_charges (node : Value Symbol Guard) :
    (InternedFreshOrdinaryStoredAllocationBudget.unfoldCharges node).1 + 2 ≤ 2 * 3 ^ Mass node ∧
      (InternedFreshOrdinaryStoredAllocationBudget.unfoldCharges node).2 + 2 ≤ 2 * 3 ^ Mass node := by
  cases node with
  | mu entry body depth ordinary =>
      have bounded := execute_charges body
      have growth := potential_mono (Nat.le_of_lt (InternedValueMass.mu_body_lt entry body depth ordinary))
      exact ⟨Nat.le_trans bounded.1 growth, Nat.le_trans bounded.2 growth⟩
  | empty | reference | node | union => exact ⟨potential_zero _, potential_zero _⟩

section Execution
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every substitution stopping heap satisfies the mass bound for any replacement environment. -/
theorem execute_bound (node : Value Symbol Guard) (environment : Environment Symbol Guard) (before : State Symbol Guard) :
    (InternedFreshOrdinaryStoredSubstitution.execute node environment before).state.nodes.next + 2 ≤
        before.nodes.next + 2 * 3 ^ Mass node ∧
      (InternedFreshOrdinaryStoredSubstitution.execute node environment before).state.edges.next + 2 ≤
        before.edges.next + 2 * 3 ^ Mass node := by
  have actual := InternedFreshOrdinaryStoredAllocationBudget.execute_bound node environment before
  have bounded := execute_charges node
  constructor <;> omega

/-- Every unfolding stopping heap satisfies the mass bound of its original complete value. -/
theorem unfold_bound (node : Value Symbol Guard) (before : State Symbol Guard) :
    (InternedFreshOrdinaryStoredSubstitution.unfold node before).state.nodes.next + 2 ≤ before.nodes.next + 2 * 3 ^ Mass node ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold node before).state.edges.next + 2 ≤ before.edges.next + 2 * 3 ^ Mass node := by
  have actual := InternedFreshOrdinaryStoredAllocationBudget.unfold_bound node before
  have bounded := unfold_charges node
  constructor <;> omega

end Execution
end MicroCFTA.InternedStoredEncodingMass
