import MicroCFTA.InternedProbeProvenance
import MicroCFTA.ConservativeEmptinessTable
import MicroCFTA.ConservativeEmptinessRows

/-!
# Untagged keys for actual closed emptiness requirements

The source table uses raw node identities. An interned reference shares its
binder identity. Closed available records exclude that reference case, so a
coherent common heap makes equal raw keys identify complete records across
constructor tags. Natural identities embed into mathematical integers here.
Machine-Int allocation and the absence of reused issued IDs remain separate
source correspondence obligations.
-/
namespace MicroCFTA.SourceEmptinessKeys
open Cache InternedBinderProtocol InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance ConservativeEmptinessExplore

/-- Read the untagged identity; empty and unresolved references have no source key. -/
def rawKey : Value Symbol Guard → Option Nat
  | .empty => none
  | .reference (.interned identity) => some identity
  | .reference _ => none
  | .node entry _ _ _ | .union entry _ _ _ | .mu entry _ _ _ => some entry.identity

/-- The logical integer key embeds the natural interner identity without a constructor tag. -/
def key (value : Value Symbol Guard) : Option Int := (rawKey value).map Int.ofNat

/-- A closed nonempty record carries an allocated constructor entry. -/
theorem entry_of_closed (value : Value Symbol Guard) (closed : value.free = [])
    (nonempty : value ≠ .empty) : ∃ entry, entryOf value = some entry := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => simp [Value.free] at closed
  | node entry | union entry | mu entry => exact ⟨entry, rfl⟩

/-- The complete allocated entry determines its untagged identity exactly. -/
theorem rawKey_of_entry (value : Value Symbol Guard) (entry : Interned NodeKey)
    (field : entryOf value = some entry) : rawKey value = some entry.identity := by
  cases value <;> simp_all [entryOf, rawKey]

/-- Closed values without an allocated key are exactly EmptyNode. -/
theorem rawKey_none_iff (value : Value Symbol Guard) (closed : value.free = []) :
    rawKey value = none ↔ value = .empty := by
  cases value with
  | empty => simp [rawKey]
  | reference name => simp [Value.free] at closed
  | node | union | mu => simp [rawKey]

/-- A closed available nonempty value has its exact entry and record in the common heap. -/
theorem stored_entry (heap : State Symbol Guard) (coherent : Coherent heap)
    (value : Value Symbol Guard) (available : Available heap value) (closed : value.free = [])
    (nonempty : value ≠ .empty) :
    ∃ entry, entryOf value = some entry ∧ heap.nodes.table entry.key = some entry ∧
      heap.nodeRecords entry.key = some value ∧ rawKey value = some entry.identity := by
  obtain ⟨entry, field⟩ := entry_of_closed value closed nonempty
  exact ⟨entry, field, InternedFreshProbeKeys.resident_entry heap coherent value available.resident entry field,
    available.resident entry field, rawKey_of_entry value entry field⟩

/-- Equal untagged keys identify complete closed resident records across all allocated tags. -/
theorem rawKey_injective (heap : State Symbol Guard) (coherent : Coherent heap)
    (left right : Value Symbol Guard) (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (same : rawKey left = rawKey right) : left = right := by
  by_cases emptyLeft : left = .empty
  · subst left
    have emptyRight := (rawKey_none_iff right rightClosed).mp same.symm
    exact emptyRight.symm
  · have nonemptyRight : right ≠ .empty := by
      intro emptyRight
      rw [emptyRight] at same
      exact emptyLeft ((rawKey_none_iff left leftClosed).mp same)
    obtain ⟨first, firstField⟩ := entry_of_closed left leftClosed emptyLeft
    obtain ⟨second, secondField⟩ := entry_of_closed right rightClosed nonemptyRight
    have identities := Option.some.inj ((rawKey_of_entry left first firstField).symm.trans
      (same.trans (rawKey_of_entry right second secondField)))
    exact InternedFreshProbeKeys.resident_identity_unique heap coherent left right
      leftAvailable.resident rightAvailable.resident first second firstField secondField identities

/-- The integer embedding preserves exact equality of the underlying raw identities. -/
theorem key_eq_iff (left right : Value Symbol Guard) : key left = key right ↔ rawKey left = rawKey right := by
  cases first : rawKey left <;> cases second : rawKey right <;> simp only [key, first, second, Option.map_none,
    Option.map_some, reduceCtorEq, Option.some.injEq, iff_self]
  constructor
  · intro same
    simpa using congrArg Int.toNat same
  · exact congrArg Int.ofNat

/-- Integer-key equality also identifies complete records under actual heap coherence. -/
theorem key_injective (heap : State Symbol Guard) (coherent : Coherent heap)
    (left right : Value Symbol Guard) (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (same : key left = key right) : left = right :=
  rawKey_injective heap coherent left right leftAvailable rightAvailable leftClosed rightClosed ((key_eq_iff left right).mp same)

/-- The proof domain contains only closed values available in one actual common heap. -/
abbrev Closed (heap : State Symbol Guard) := {value : Value Symbol Guard // Available heap value ∧ value.free = []}

/-- EmptyNode belongs to every certified closed domain. -/
def empty (heap : State Symbol Guard) : Closed heap := ⟨.empty, empty_available heap, rfl⟩

/-- Convert a certified source value to the completed item used by the finite table. -/
def item (value : Closed heap) : Item :=
  match key value.val with
  | none => .empty
  | some identity => .resident identity true

/-- An empty item identifies the actual certified EmptyNode, rather than a raw alias. -/
theorem item_empty_iff (value : Closed heap) : item value = .empty ↔ value = empty heap := by
  have raw := rawKey_none_iff value.val value.property.2
  cases found : rawKey value.val with
  | none =>
      have same := raw.mp found
      have equal : value = empty heap := Subtype.ext same
      simp [equal, item, key, empty, rawKey]
  | some identity =>
      have different : value ≠ empty heap := by
        intro same
        have fields := congrArg Subtype.val same
        rw [fields] at found
        cases found
      simp [item, key, found, different]

/-- Classify the actual untagged item against exactly the stored finite table keys. -/
def classify (table : Table) (value : Closed heap) : ConservativeEmptiness.Requirement (ConservativeEmptinessTable.Key table) :=
  ConservativeEmptinessTable.classify table (item value)

/-- Search complete inventory records by their untagged logical integer identity. -/
def find (identity : Int) : List (Closed heap) → Option (Closed heap)
  | [] => none
  | value :: rest => if key value.val = some identity then some value else find identity rest

/-- A successful inventory read retains its exact key and original record occurrence. -/
theorem find_sound (identity : Int) (inventory : List (Closed heap)) (value : Closed heap)
    (found : find identity inventory = some value) : value ∈ inventory ∧ key value.val = some identity := by
  induction inventory with
  | nil => simp [find] at found
  | cons first rest ih =>
      simp only [find] at found
      split at found
      · rename_i same
        cases Option.some.inj found
        exact ⟨List.mem_cons_self, same⟩
      · obtain ⟨member, same⟩ := ih found
        exact ⟨List.mem_cons_of_mem _ member, same⟩

/-- A key carried by any original inventory record has a successful finite search. -/
theorem find_complete (identity : Int) (inventory : List (Closed heap))
    (present : ∃ value ∈ inventory, key value.val = some identity) : ∃ value, find identity inventory = some value := by
  induction inventory with
  | nil => simp at present
  | cons first rest ih =>
      by_cases same : key first.val = some identity
      · exact ⟨first, by simp [find, same]⟩
      · obtain ⟨value, member, actual⟩ := present
        have tail : value ∈ rest := by
          rcases List.mem_cons.mp member with equal | selected
          · subst value; exact False.elim (same actual)
          · exact selected
        obtain ⟨value, found⟩ := ih ⟨value, tail, actual⟩
        exact ⟨value, by simp [find, same, found]⟩

/-- Every stored table key must have an actual complete certified inventory record. -/
def Covered (table : Table) (inventory : List (Closed heap)) : Prop :=
  ∀ identity ∈ table.map Prod.fst, ∃ value ∈ inventory, key value.val = some identity

/-- Read a finite table key from the original complete inventory; empty is an unused fallback under coverage. -/
def read (table : Table) (inventory : List (Closed heap)) (state : ConservativeEmptinessTable.Key table) : Closed heap :=
  (find state.val inventory).getD (empty heap)

/-- Covered table reads recover an actual complete inventory record with the exact untagged key. -/
theorem read_key (table : Table) (inventory : List (Closed heap)) (covered : Covered table inventory)
    (state : ConservativeEmptinessTable.Key table) :
    read table inventory state ∈ inventory ∧ key (read table inventory state).val = some state.val := by
  obtain ⟨value, found⟩ := find_complete state.val inventory (covered state.val state.property)
  have actual := find_sound state.val inventory value found
  simpa only [read, found, Option.getD_some] using actual

/-- Finite classification has literal record readback on the certified source domain. -/
theorem classify_readback (heap : State Symbol Guard) (coherent : Coherent heap)
    (table : Table) (inventory : List (Closed heap)) (covered : Covered table inventory) (value : Closed heap) :
    match classify table value with
    | .empty => value = empty heap
    | .outside => True
    | .inside state => value = read table inventory state := by
  unfold classify
  cases classified : item value with
  | empty => exact (item_empty_iff value).mp classified
  | resident identity closed =>
      have actual : key value.val = some identity := by
        unfold item at classified
        split at classified
        · cases classified
        · rename_i found
          exact Item.resident.inj classified |>.1 ▸ found
      by_cases present : identity ∈ table.map Prod.fst
      · simp only [ConservativeEmptinessTable.classify, present, ↓reduceDIte]
        apply Subtype.ext
        exact key_injective heap coherent value.val (read table inventory ⟨identity, present⟩).val
          value.property.1 (read table inventory ⟨identity, present⟩).property.1
          value.property.2 (read table inventory ⟨identity, present⟩).property.2
          (actual.trans (read_key table inventory covered ⟨identity, present⟩).2.symm)
      · simp only [ConservativeEmptinessTable.classify, present, ↓reduceDIte]

/-- Any operations on the certified domain with the actual empty value satisfy exact physical Readback. -/
theorem readback (heap : State Symbol Guard) (coherent : Coherent heap)
    (table : Table) (inventory : List (Closed heap)) (covered : Covered table inventory)
    (ops : EqualityReduction.Operations (Closed heap) Symbol) (emptyField : ops.empty = empty heap) :
    ConservativeEmptinessRows.Readback ops (read table inventory) (classify table) := by
  intro value
  have actual := classify_readback heap coherent table inventory covered value
  cases classified : classify table value with
  | empty =>
      have same : value = empty heap := by simpa only [classified] using actual
      simpa only [classified] using same.trans emptyField.symm
  | outside => trivial
  | inside state => simpa only [classified] using actual

end MicroCFTA.SourceEmptinessKeys
