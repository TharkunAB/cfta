import MicroCFTA.EnumerationState

/-!
# Unused modeled recursion-key shapes at one native handle

The original term supplies the finite shape carrier.
Inherited histories can only remove unused shapes.
Inserting the exact fresh key strictly reduces the remaining list.
This measure does not bound the number of native handles.
-/
namespace MicroCFTA.SourcePruningEnumerationKeyShapeBudget
open EnumerationState

/-- Keep the finite carrier shapes whose exact handle key is absent from this history. -/
def unused (carrier : List (List (List (List Nat)))) (handle : Nat)
    (history : List RecursionKey) : List (List (List (List Nat))) :=
  carrier.filter fun shape => decide ((⟨handle, shape⟩ : RecursionKey) ∉ history)

private theorem unused_filter
    (carrier : List (List (List (List Nat)))) (handle : Nat) (before after : List RecursionKey)
    (included : ∀ key ∈ before, key ∈ after) :
    unused carrier handle after = (unused carrier handle before).filter
      (fun shape => decide ((⟨handle, shape⟩ : RecursionKey) ∉ after)) := by
  unfold unused
  rw [List.filter_filter]
  apply congrArg (fun predicate => carrier.filter predicate)
  funext shape
  by_cases absent : (⟨handle, shape⟩ : RecursionKey) ∉ after
  · have original : (⟨handle, shape⟩ : RecursionKey) ∉ before :=
      fun member => absent (included _ member)
    simp only [decide_eq_true absent, decide_eq_true original, Bool.and_self]
  · simp only [decide_eq_false absent, Bool.false_and]

/-- The unused shape count is bounded by the original finite carrier length. -/
theorem unused_bounded
    (carrier : List (List (List (List Nat)))) (handle : Nat) (history : List RecursionKey) :
    (unused carrier handle history).length ≤ carrier.length :=
  List.filter_sublist.length_le

/-- Inheriting more keys cannot increase the unused shape count at a fixed handle. -/
theorem unused_mono
    (carrier : List (List (List (List Nat)))) (handle : Nat) (before after : List RecursionKey)
    (included : ∀ key ∈ before, key ∈ after) :
    (unused carrier handle after).length ≤ (unused carrier handle before).length := by
  rw [unused_filter carrier handle before after included]
  exact List.filter_sublist.length_le

/-- Inserting the same fresh key strictly decreases the original finite shape budget. -/
theorem unused_insert_lt
    (carrier : List (List (List (List Nat)))) (key : RecursionKey) (history : List RecursionKey)
    (member : key.tries ∈ carrier) (fresh : key ∉ history) :
    (unused carrier key.node (key :: history).eraseDups).length <
      (unused carrier key.node history).length := by
  have included : ∀ old ∈ history, old ∈ (key :: history).eraseDups := by
    intro old present
    simp only [List.mem_eraseDups, List.mem_cons]
    exact Or.inr present
  have sublist : List.Sublist (unused carrier key.node (key :: history).eraseDups)
      (unused carrier key.node history) := by
    rw [unused_filter carrier key.node history (key :: history).eraseDups included]
    exact List.filter_sublist
  have sameKey : (⟨key.node, key.tries⟩ : RecursionKey) = key := by cases key; rfl
  have before : key.tries ∈ unused carrier key.node history := by
    simp only [unused, List.mem_filter, decide_eq_true_eq, sameKey]
    exact ⟨member, fresh⟩
  have after : key.tries ∉ unused carrier key.node (key :: history).eraseDups := by
    simp only [unused, List.mem_filter, decide_eq_true_eq, sameKey, List.mem_eraseDups,
      List.mem_cons, true_or, not_true_eq_false, and_false, not_false_eq_true]
  apply Nat.lt_of_not_ge
  intro size
  exact after ((sublist.eq_of_length_le size).symm ▸ before)

end MicroCFTA.SourcePruningEnumerationKeyShapeBudget
