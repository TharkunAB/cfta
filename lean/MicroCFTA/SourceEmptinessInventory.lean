import MicroCFTA.SourceEmptinessKeys

/-!
# Physical inventory from actual finite table entries

The inventory contains the complete values from the entry list. Per-entry
availability, closure, and exact untagged keys derive table coverage. The
table must retain exactly those entry keys. No answer function or separate
inventory coverage premise is required. Native entry construction and the
machine-Int identity correspondence remain separate obligations.
-/
namespace MicroCFTA.SourceEmptinessInventory
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open ConservativeEmptinessExplore SourceEmptinessKeys

/-- Each actual entry retains a closed available value with its exact untagged key. -/
def Records (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard)) : Prop :=
  ∀ entry ∈ entries, Available heap entry.2 ∧ entry.2.free = [] ∧ key entry.2 = some entry.1

/-- Certify the complete values in the actual entry list without changing their order. -/
def inventory (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) : List (Closed heap) :=
  entries.attach.map (fun entry => ⟨entry.val.2, (records entry.val entry.property).1,
    (records entry.val entry.property).2.1⟩)

/-- The certified inventory retains exactly the original complete values in entry order. -/
theorem inventory_values (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) :
    (inventory heap entries records).map Subtype.val = entries.map Prod.snd := by
  simp only [inventory, List.map_map, Function.comp_def]
  exact List.attach_map_val

/-- Every original entry occurs in the computed certified inventory. -/
theorem inventory_member (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) (entry : Int × Value Symbol Guard) (member : entry ∈ entries) :
    (⟨entry.2, (records entry member).1, (records entry member).2.1⟩ : Closed heap) ∈
      inventory heap entries records := by
  apply List.mem_map.mpr
  exact ⟨⟨entry, member⟩, by simp, rfl⟩

/-- Literal entry keys derive coverage of the table by its own complete values. -/
theorem covered (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) (table : Table)
    (sameKeys : table.map Prod.fst = entries.map Prod.fst) :
    SourceEmptinessKeys.Covered table (inventory heap entries records) := by
  intro identity present
  rw [sameKeys] at present
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  refine ⟨⟨entry.2, (records entry member).1, (records entry member).2.1⟩,
    inventory_member heap entries records entry member, ?_⟩
  simpa only [same] using (records entry member).2.2

/-- Read a table key from the complete values in its own actual entry list. -/
def read (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) (table : Table) (state : ConservativeEmptinessTable.Key table) : Closed heap :=
  SourceEmptinessKeys.read table (inventory heap entries records) state

/-- Every computed read has its exact table key and an original complete entry value. -/
theorem read_record (heap : State Symbol Guard) (entries : List (Int × Value Symbol Guard))
    (records : Records heap entries) (table : Table)
    (sameKeys : table.map Prod.fst = entries.map Prod.fst) (state : ConservativeEmptinessTable.Key table) :
    key (read heap entries records table state).val = some state.val ∧
      ∃ entry ∈ entries, entry.2 = (read heap entries records table state).val := by
  have actual := SourceEmptinessKeys.read_key table (inventory heap entries records)
    (covered heap entries records table sameKeys) state
  refine ⟨actual.2, ?_⟩
  have member : (read heap entries records table state).val ∈ entries.map Prod.snd := by
    rw [← inventory_values heap entries records]
    exact List.mem_map.mpr ⟨_, actual.1, rfl⟩
  exact List.mem_map.mp member

/-- Coherent actual entry records derive exact table readback without a supplied inventory. -/
theorem readback (heap : State Symbol Guard) (coherent : Coherent heap)
    (entries : List (Int × Value Symbol Guard)) (records : Records heap entries) (table : Table)
    (sameKeys : table.map Prod.fst = entries.map Prod.fst)
    (ops : EqualityReduction.Operations (Closed heap) Symbol)
    (emptyField : ops.empty = SourceEmptinessKeys.empty heap) :
    ConservativeEmptinessRows.Readback ops (read heap entries records table)
      (SourceEmptinessKeys.classify table) :=
  SourceEmptinessKeys.readback heap coherent table (inventory heap entries records)
    (covered heap entries records table sameKeys) ops emptyField

end MicroCFTA.SourceEmptinessInventory
