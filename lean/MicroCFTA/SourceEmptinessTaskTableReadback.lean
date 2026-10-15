import MicroCFTA.SourceEmptinessTaskTrace

/-!
# Physical readback for completed task tables

The actual entry values supply the finite table's semantic reads. Coherent
closed records identify equal untagged keys. Each completed task requirement
then carries its own accepted smaller witness through classification. These
proofs do not require total projection or intersection on the final heap.
-/
namespace MicroCFTA.SourceEmptinessTaskTableReadback
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEmptinessTaskTrace
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "TaskState" => SourceEmptinessTasks.State
local notation "Task" => SourceEmptinessTasks.Task Symbol Guard
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Entries" => DelayedEmptinessExplore.Table Task Value

/-- A successful delayed lookup retains its original entry and exact key. -/
theorem lookup_sound (identity : Int) (entries : Entries) (entry : DelayedEmptinessExplore.Entry Task Value)
    (found : DelayedEmptinessExplore.lookup identity entries = some entry) :
    entry ∈ entries ∧ entry.key = identity := by
  induction entries with
  | nil => cases found
  | cons first rest ih =>
      by_cases same : identity = first.key
      · have actual : first = entry := by
          simpa only [DelayedEmptinessExplore.lookup, same, ↓reduceIte, Option.some.injEq] using found
        subst entry
        exact ⟨List.mem_cons_self, same.symm⟩
      · have tail : DelayedEmptinessExplore.lookup identity rest = some entry := by
          simpa only [DelayedEmptinessExplore.lookup, same, ↓reduceIte] using found
        obtain ⟨member, key⟩ := ih tail
        exact ⟨List.mem_cons_of_mem _ member, key⟩

/-- Reading completed tasks commutes with first lookup in the original entry list. -/
theorem lookup_table (state : TaskState width Symbol Guard) (entries : Entries) (identity : Int) :
    ConservativeEmptinessExplore.lookup identity (table state entries) =
      (DelayedEmptinessExplore.lookup identity entries).map
        (fun entry => entry.rows.map (List.map (readItem state))) := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : identity = first.key
      · simp only [table, List.map_cons, ConservativeEmptinessExplore.lookup,
          DelayedEmptinessExplore.lookup, same, ↓reduceIte, Option.map_some]
      · simpa only [table, List.map_cons, ConservativeEmptinessExplore.lookup,
          DelayedEmptinessExplore.lookup, same, ↓reduceIte] using ih

/-- The actual completed entry inventory supplies each finite table value. -/
def valueAt (state : TaskState width Symbol Guard) (entries : Entries)
    (records : SourceEmptinessInventory.Records (heap state) (SourceDelayedEmptinessInventory.entries entries))
    (key : ConservativeEmptinessTable.Key (table state entries)) : Value :=
  (SourceEmptinessInventory.read (heap state) (SourceDelayedEmptinessInventory.entries entries)
    records (table state entries) key).val

/-- Coherence identifies the first stored entry with the table's actual inventory read. -/
theorem entry_value (state : TaskState width Symbol Guard) (entries : Entries)
    (records : SourceEmptinessInventory.Records (heap state) (SourceDelayedEmptinessInventory.entries entries))
    (coherent : InternedRecordCoherence.Coherent (heap state))
    (key : ConservativeEmptinessTable.Key (table state entries)) :
    ∃ entry, DelayedEmptinessExplore.lookup key.val entries = some entry ∧
      entry.value = valueAt state entries records key := by
  have present : key.val ∈ entries.map DelayedEmptinessExplore.Entry.key := by
    simpa only [table_keys] using key.property
  cases found : DelayedEmptinessExplore.lookup key.val entries with
  | none => exact False.elim ((DelayedEmptinessExplore.lookup_none_iff _ _).mp found present)
  | some entry =>
      have actual := lookup_sound key.val entries entry found
      have member : (entry.key, entry.value) ∈ SourceDelayedEmptinessInventory.entries entries :=
        List.mem_map.mpr ⟨entry, actual.1, rfl⟩
      have stored := records _ member
      have read := SourceEmptinessInventory.read_record (heap state)
        (SourceDelayedEmptinessInventory.entries entries) records (table state entries)
        ((table_keys state entries).trans (SourceDelayedEmptinessInventory.entries_keys entries).symm) key
      exact ⟨entry, rfl, SourceEmptinessKeys.key_injective (heap state) coherent _ _ stored.1
        (SourceEmptinessInventory.read (heap state) _ records (table state entries) key).property.1
        stored.2.1 (SourceEmptinessInventory.read (heap state) _ records (table state entries) key).property.2
        (stored.2.2.trans ((congrArg some actual.2).trans read.1.symm))⟩

/-- A closed resident value has exact classifier readback without arbitrary native operations. -/
theorem classified (state : TaskState width Symbol Guard) (entries : Entries)
    (records : SourceEmptinessInventory.Records (heap state) (SourceDelayedEmptinessInventory.entries entries))
    (coherent : InternedRecordCoherence.Coherent (heap state))
    (value : Value) (available : Available (heap state) value) (closed : value.free = []) :
    match ConservativeEmptinessTable.classify (table state entries) (encode value) with
    | .empty => value = .empty
    | .outside => True
    | .inside key => value = valueAt state entries records key := by
  let certified : SourceEmptinessKeys.Closed (heap state) := ⟨value, available, closed⟩
  have actual := SourceEmptinessKeys.classify_readback (heap state) coherent (table state entries)
    (SourceEmptinessInventory.inventory (heap state) (SourceDelayedEmptinessInventory.entries entries) records)
    (SourceEmptinessInventory.covered (heap state) _ records _
      ((table_keys state entries).trans (SourceDelayedEmptinessInventory.entries_keys entries).symm)) certified
  unfold SourceEmptinessKeys.classify at actual
  rw [← encode_closed (heap state) certified] at actual
  simp only [certified] at actual
  cases classification : ConservativeEmptinessTable.classify (table state entries) (encode value) with
  | empty => exact congrArg Subtype.val (by simpa only [classification] using actual)
  | outside => trivial
  | inside key => exact congrArg Subtype.val (by simpa only [classification] using actual)

/-- An actual smaller accepted value supplies the classified finite-table obligation. -/
theorem value_obligation (state : TaskState width Symbol Guard) (entries : Entries)
    (records : SourceEmptinessInventory.Records (heap state) (SourceDelayedEmptinessInventory.entries entries))
    (coherent : InternedRecordCoherence.Coherent (heap state))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (parent part : Term Symbol) (value : Value) (available : Available (heap state) value) (closed : value.free = [])
    (accepted : meaning holds ambient value part) (smaller : part.height < parent.height) :
    ConservativeEmptiness.Obligation (fun key => meaning holds ambient (valueAt state entries records key))
      Term.height parent (ConservativeEmptinessTable.classify (table state entries) (encode value)) := by
  have readback := classified state entries records coherent value available closed
  cases classification : ConservativeEmptinessTable.classify (table state entries) (encode value) with
  | empty =>
      have empty : value = .empty := by simpa only [classification] using readback
      subst value
      simp only [meaning] at accepted
  | outside => trivial
  | inside key =>
      have same : value = valueAt state entries records key := by simpa only [classification] using readback
      exact ⟨part, by simpa only [same] using accepted, smaller⟩

end MicroCFTA.SourceEmptinessTaskTableReadback
