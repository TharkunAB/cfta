import MicroCFTA.InternedSourceCrush

/-!
# Finite identity inventory of the actual source crush

Every visited identity comes from the current source reservation counter.
The shared visited set has no duplicate. This includes arbitrary nested Mu
records and union members. The traversal has no caller fuel bound.
-/
namespace MicroCFTA.InternedSourceCrush
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance

/-- The visited source identities are distinct and below the actual issued counter. -/
def Inventory (state : State Symbol Guard) (seen : List Nat) : Prop :=
  seen.Nodup ∧ ∀ identity ∈ seen, identity < state.nodes.next

/-- An unseen issued identity extends the actual visited set. -/
theorem add_inventory (state : State Symbol Guard) (seen : List Nat) (identity : Nat)
    (inventory : Inventory state seen) (fresh : identity ∉ seen) (bound : identity < state.nodes.next) :
    Inventory state (identity :: seen) := by
  refine ⟨List.nodup_cons.mpr ⟨fresh, inventory.1⟩, ?_⟩
  intro other member
  rcases List.mem_cons.mp member with rfl | old
  · exact bound
  · exact inventory.2 other old

mutual
/-- Actual source traversal retains a finite distinct inventory of issued node identities. -/
theorem visit_inventory (plain : Guard → Bool) (value : Value Symbol Guard) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value)
    (inventory : Inventory state seen) : Inventory state (visit plain value seen).2 := by
  cases value with
  | empty | reference => simpa only [visit] using inventory
  | node entry edges depth free =>
      rw [visit]
      split
      · exact inventory
      · rename_i fresh
        have bound := InternedNodeIdentityFootprint.available_below state coherent _ available entry.identity (.entry _ entry rfl rfl)
        exact visitEdges_inventory plain edges _ state coherent (fun child member => available.children child member)
          (add_inventory state seen entry.identity inventory fresh bound)
  | union entry values depth free =>
      rw [visit]
      split
      · exact inventory
      · rename_i fresh
        have bound := InternedNodeIdentityFootprint.available_below state coherent _ available entry.identity (.entry _ entry rfl rfl)
        exact visitMany_inventory plain values _ state coherent (fun child member => available.children child member)
          (add_inventory state seen entry.identity inventory fresh bound)
  | mu entry body depth ordinary =>
      rw [visit]
      split
      · exact inventory
      · rename_i fresh
        have bound := InternedNodeIdentityFootprint.available_below state coherent _ available entry.identity (.entry _ entry rfl rfl)
        exact visit_inventory plain body _ state coherent (available.children body (by simp [children]))
          (add_inventory state seen entry.identity inventory fresh bound)
termination_by sizeOf value

/-- Every ordered child reads and returns the same finite identity namespace. -/
theorem visitMany_inventory (plain : Guard → Bool) (values : List (Value Symbol Guard)) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state) (available : ∀ value ∈ values, Available state value)
    (inventory : Inventory state seen) : Inventory state (visitMany plain values seen).2 := by
  cases values with
  | nil => simpa only [visitMany] using inventory
  | cons first rest =>
      rw [visitMany]
      exact visitMany_inventory plain rest _ state coherent
        (fun value member => available value (List.mem_cons_of_mem first member))
        (visit_inventory plain first seen state coherent (available first List.mem_cons_self) inventory)
termination_by sizeOf values

/-- Original edge children retain finite visited identities through each shared-state child fold. -/
theorem visitEdges_inventory (plain : Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (seen : List Nat)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (inventory : Inventory state seen) : Inventory state (visitEdges plain edges seen).2 := by
  cases edges with
  | nil => simpa only [visitEdges] using inventory
  | cons first rest =>
      cases first with
      | mk entry children =>
          rw [visitEdges]
          exact visitEdges_inventory plain rest _ state coherent
            (fun value member => available value (by simp [member]))
            (visitMany_inventory plain children seen state coherent
              (fun value member => available value (by simp [EdgeValue.children, member])) inventory)
termination_by sizeOf edges
end

/-- The source predicate visits at most the actual number of issued node identities. -/
theorem empty_inventory_bound (plain : Guard → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    (visit plain value []).2.Nodup ∧ (visit plain value []).2.length ≤ state.nodes.next := by
  have inventory := visit_inventory plain value [] state coherent available ⟨by simp, by simp⟩
  have subset : (visit plain value []).2 ⊆ List.range state.nodes.next := by
    intro identity member
    exact List.mem_range.mpr (inventory.2 identity member)
  exact ⟨inventory.1, by simpa only [List.length_range] using inventory.1.length_le_of_subset subset⟩

end MicroCFTA.InternedSourceCrush
