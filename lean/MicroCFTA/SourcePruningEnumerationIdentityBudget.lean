import MicroCFTA.SourcePruningEnumerationKeyShapeBudget

/-!
# Recursion-key budgets under identity renaming

Injective handle renaming preserves key equality and history membership.
The unused shape list and its strict decrease remain equal.
This result supplies no finite handle carrier or native execution bound.
Output order needs a relation that also preserves relevant identity order.
No cache key, child graph, effect, or cost is renamed here.
-/
namespace MicroCFTA.SourcePruningEnumerationIdentityBudget
open EnumerationState SourcePruningEnumerationKeyShapeBudget

/-- Rename only the node handle of a recursion key. -/
def renameKey (rename : Nat → Nat) (key : RecursionKey) : RecursionKey :=
  ⟨rename key.node, key.tries⟩

/-- Map a history without changing its order or removing duplicates. -/
def renameHistory (rename : Nat → Nat) (history : List RecursionKey) : List RecursionKey :=
  history.map (renameKey rename)

/-- Key construction commutes with handle renaming and leaves suspended paths unchanged. -/
theorem renameKey_recursionKey (rename : Nat → Nat) (handle : Nat) (scs : List Suspended) :
    renameKey rename (recursionKey handle scs) = recursionKey (rename handle) scs := rfl

/-- Injective handle renaming preserves both directions of complete key equality. -/
theorem renameKey_eq_iff (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (first second : RecursionKey) :
    renameKey rename first = renameKey rename second ↔ first = second := by
  cases first
  cases second
  simp only [renameKey, RecursionKey.mk.injEq]
  constructor
  · rintro ⟨same, tries⟩
    exact ⟨injective same, tries⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- A renamed key occurs exactly when its original occurs in the original history. -/
theorem mem_renameHistory_iff (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (key : RecursionKey) (history : List RecursionKey) :
    renameKey rename key ∈ renameHistory rename history ↔ key ∈ history := by
  change renameKey rename key ∈ history.map (renameKey rename) ↔ key ∈ history
  constructor
  · intro member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    have equal := (renameKey_eq_iff rename injective original key).mp same
    exact equal ▸ present
  · intro member
    exact List.mem_map.mpr ⟨key, member, rfl⟩

/-- Removing duplicate keys preserves the same membership correspondence. -/
theorem mem_renameHistory_eraseDups_iff (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (key : RecursionKey) (history : List RecursionKey) :
    renameKey rename key ∈ (renameHistory rename history).eraseDups ↔
      key ∈ history.eraseDups := by
  simp only [List.mem_eraseDups, mem_renameHistory_iff rename injective]

/-- Duplicate history entries do not change the unused shape list. -/
theorem unused_eraseDups (carrier : List (List (List (List Nat))))
    (handle : Nat) (history : List RecursionKey) :
    unused carrier handle history.eraseDups = unused carrier handle history := by
  simp only [unused, List.mem_eraseDups]

/-- The complete unused shape list is invariant under injective handle renaming. -/
theorem unused_rename (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (carrier : List (List (List (List Nat)))) (handle : Nat) (history : List RecursionKey) :
    unused carrier (rename handle) (renameHistory rename history) =
      unused carrier handle history := by
  change carrier.filter
      (fun shape => decide (renameKey rename ⟨handle, shape⟩ ∉ renameHistory rename history)) =
    carrier.filter (fun shape => decide ((⟨handle, shape⟩ : RecursionKey) ∉ history))
  simp only [mem_renameHistory_iff rename injective]

/-- Fixed-handle strict decrease holds before renaming exactly when it holds afterwards. -/
theorem unused_insert_lt_iff (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (carrier : List (List (List (List Nat)))) (key : RecursionKey) (history : List RecursionKey) :
    (unused carrier (rename key.node)
      (renameKey rename key :: renameHistory rename history).eraseDups).length <
        (unused carrier (rename key.node) (renameHistory rename history)).length ↔
    (unused carrier key.node (key :: history).eraseDups).length <
      (unused carrier key.node history).length := by
  change (unused carrier (rename key.node)
      (renameHistory rename (key :: history)).eraseDups).length <
        (unused carrier (rename key.node) (renameHistory rename history)).length ↔ _
  simp only [unused_eraseDups, unused_rename rename injective]

/-- An actual fresh-key insertion retains the existing strict budget theorem after renaming. -/
theorem renamed_unused_insert_lt (rename : Nat → Nat)
    (injective : ∀ {first second}, rename first = rename second → first = second)
    (carrier : List (List (List (List Nat)))) (key : RecursionKey) (history : List RecursionKey)
    (member : key.tries ∈ carrier) (fresh : key ∉ history) :
    (unused carrier (rename key.node)
      (renameKey rename key :: renameHistory rename history).eraseDups).length <
        (unused carrier (rename key.node) (renameHistory rename history)).length :=
  (unused_insert_lt_iff rename injective carrier key history).mpr
    (unused_insert_lt carrier key history member fresh)

end MicroCFTA.SourcePruningEnumerationIdentityBudget
